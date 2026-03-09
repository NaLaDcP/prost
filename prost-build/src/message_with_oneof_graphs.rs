use std::collections::HashMap;
use std::fs;
use std::io;
use std::path::PathBuf;

use petgraph::acyclic::Acyclic;
use petgraph::algo::has_path_connecting;
use petgraph::data::Build;
use petgraph::dot::Dot;
use petgraph::graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use petgraph::Graph;

use prost_types::{
    field_descriptor_proto::{Label, Type},
    DescriptorProto, FileDescriptorProto,
};

/// Distinguishes the kind of graph edge.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MessageOneOfEdge {
    Message,
    OneOf(String),
}

impl MessageOneOfEdge {
    pub fn value(&self) -> u8 {
        match self {
            Self::Message => 1,
            Self::OneOf(_) => 2,
        }
    }
}

/// Builds a graph containing only message nodes.
///
/// Edges are typed to distinguish plain message nesting from links through a oneof.
pub struct MessageWithOneofGraphs {
    index: HashMap<String, NodeIndex>,
    graph: Acyclic<Graph<String, MessageOneOfEdge>>,
    messages: HashMap<String, DescriptorProto>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MessageOneOfPath {
    pub upward: Vec<NodeIndex>,
    pub downward: Vec<NodeIndex>,
    /// OneOf names for each edge in `upward`, same order and length = `upward.len() - 1`.
    pub upward_oneof_variants: Vec<String>,
    /// OneOf names for each edge in `downward`, same order and length = `downward.len() - 1`.
    pub downward_oneof_variants: Vec<String>,
}

impl MessageWithOneofGraphs {
    pub fn new<'a>(
        files: impl Iterator<Item = &'a FileDescriptorProto>,
        dot_file_name: Option<&str>,
    ) -> MessageWithOneofGraphs {
        let mut msg_graph = MessageWithOneofGraphs {
            index: HashMap::new(),
            graph: Acyclic::new(),
            messages: HashMap::new(),
        };

        for file in files {
            let package = format!(
                "{}{}",
                if file.package.is_some() { "." } else { "" },
                file.package.as_deref().unwrap_or("")
            );
            for msg in &file.message_type {
                msg_graph.add_message(&package, msg);
            }
        }

        if let Some(file_name) = dot_file_name {
            let _ = msg_graph.write_dot(file_name);
        }
        msg_graph
    }

    fn get_or_insert_index(&mut self, node_name: String) -> NodeIndex {
        assert_eq!(b'.', node_name.as_bytes()[0]);
        if let Some(index) = self.index.get(&node_name).copied() {
            return index;
        }

        let index = self.graph.add_node(node_name.clone());
        self.index.insert(node_name, index);
        index
    }

    fn add_message(&mut self, package: &str, msg: &DescriptorProto) {
        let msg_name = format!("{}.{}", package, msg.name.as_ref().unwrap());
        let msg_index = self.get_or_insert_index(msg_name.clone());

        for field in &msg.field {
            if field.r#type() == Type::Message && field.label() != Label::Repeated {
                let field_index = self.get_or_insert_index(field.type_name.clone().unwrap());
                if let Some(oneof_index) = field.oneof_index {
                    let oneof = &msg.oneof_decl[oneof_index as usize];
                    let oneof_name = format!("{}.{}", msg_name, oneof.name.as_ref().unwrap());

                    self.graph
                        .try_add_edge(msg_index, field_index, MessageOneOfEdge::OneOf(oneof_name))
                        .expect("adding OneOf edge introduced a cycle");
                } else {
                    self.graph
                        .try_add_edge(msg_index, field_index, MessageOneOfEdge::Message)
                        .expect("adding message edge introduced a cycle");
                }
            }
        }
        self.messages.insert(msg_name.clone(), msg.clone());

        for nested in &msg.nested_type {
            self.add_message(&msg_name, nested);
        }
    }

    pub fn get_message(&self, message: &str) -> Option<&DescriptorProto> {
        self.messages.get(message)
    }

    pub fn is_nested(&self, outer: &str, inner: &str) -> bool {
        let outer = match self.index.get(outer) {
            Some(outer) => *outer,
            None => return false,
        };
        let inner = match self.index.get(inner) {
            Some(inner) => *inner,
            None => return false,
        };

        has_path_connecting(&self.graph, outer, inner, None)
    }

    pub fn edge_value(&self, source: &str, target: &str) -> Option<u8> {
        let source = *self.index.get(source)?;
        let target = *self.index.get(target)?;

        let edge = self.graph.find_edge(source, target)?;
        self.graph.edge_weight(edge).map(|kind| kind.value())
    }

    /// Returns all graph roots (nodes without incoming edges).
    fn root_nodes(graph: &Acyclic<Graph<String, MessageOneOfEdge>>) -> Vec<NodeIndex> {
        graph
            .node_indices()
            .filter(|&node| {
                graph
                    .neighbors_directed(node, Direction::Incoming)
                    .next()
                    .is_none()
            })
            .collect()
    }

    fn dfs(
        &self,
        current: NodeIndex,
        current_path: &mut Vec<NodeIndex>,
        current_oneof_variants: &mut Vec<String>,
        paths: &mut Vec<(Vec<NodeIndex>, Vec<String>)>,
    ) {
        let outgoing_edges = self
            .graph
            .edges_directed(current, Direction::Outgoing)
            .collect::<Vec<_>>();

        if outgoing_edges.is_empty() {
            paths.push((current_path.clone(), current_oneof_variants.clone()));
            return;
        }

        if outgoing_edges
            .iter()
            .any(|edge| !matches!(edge.weight(), MessageOneOfEdge::OneOf(_)))
        {
            paths.push((current_path.clone(), current_oneof_variants.clone()));
            return;
        }

        for edge in outgoing_edges {
            let MessageOneOfEdge::OneOf(oneof_name) = edge.weight() else {
                unreachable!("validated above");
            };
            let next = edge.target();
            current_path.push(next);
            current_oneof_variants.push(oneof_name.clone());
            self.dfs(next, current_path, current_oneof_variants, paths);
            current_oneof_variants.pop();
            current_path.pop();
        }
    }

    ///
    /// Traversal starts from root nodes (no incoming edges) and follows each
    /// root branch in depth-first order.
    /// A branch is stopped immediately when a node has more than one outgoing
    /// edge, or when its unique outgoing edge is not `OneOf`.
    ///
    /// Each returned path carries:
    /// - node indices in both directions (`upward`/`downward`)
    /// - oneof edge payloads in both directions (`*_oneof_variants`)
    pub fn oneof_parent_paths_for_wrapped_messages(&self) -> Vec<MessageOneOfPath> {
        let mut paths = Vec::new();

        for root in Self::root_nodes(&self.graph) {
            let mut current_path = vec![root];
            let mut current_oneof_variants = Vec::new();
            let mut raw_paths = Vec::new();
            self.dfs(
                root,
                &mut current_path,
                &mut current_oneof_variants,
                &mut raw_paths,
            );
            for (downward, downward_oneof_variants) in raw_paths {
                if downward.len() < 2 {
                    continue;
                }

                let upward = downward.iter().rev().copied().collect();
                let upward_oneof_variants = downward_oneof_variants.iter().rev().cloned().collect();
                paths.push(MessageOneOfPath {
                    upward,
                    downward,
                    upward_oneof_variants,
                    downward_oneof_variants,
                });
            }
        }

        paths
    }

    pub fn to_dot(&self) -> String {
        format!("{:?}", Dot::new(&self.graph))
    }

    pub fn write_dot(&self, file_name: &str) -> io::Result<PathBuf> {
        let out = std::env::var("OUT_DIR")
            .map(PathBuf::from)
            .map_err(|e| io::Error::new(io::ErrorKind::NotFound, e.to_string()))?;
        let path = out.join(file_name);
        fs::write(&path, self.to_dot())?;
        Ok(path)
    }

    pub fn node_name(&self, node: NodeIndex) -> Option<&str> {
        self.graph.node_weight(node).map(String::as_str)
    }
}
