use std::collections::HashMap;

use petgraph::acyclic::Acyclic;
use petgraph::algo::has_path_connecting;
use petgraph::data::Build;
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
    pub fn new<'a>(files: impl Iterator<Item = &'a FileDescriptorProto>) -> MessageWithOneofGraphs {
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

    /// Returns node indices for messages wrapped in a union:
    /// at least one incoming `OneOf` edge and no outgoing `OneOf` edge.
    pub fn message_wrapped_in_union_indices(&self) -> Vec<NodeIndex> {
        let mut result = Vec::new();

        for node in self.graph.node_indices() {
            let has_incoming_oneof = self
                .graph
                .edges_directed(node, Direction::Incoming)
                .any(|edge| matches!(edge.weight(), MessageOneOfEdge::OneOf(_)));
            let has_outgoing_oneof = self
                .graph
                .edges_directed(node, Direction::Outgoing)
                .any(|edge| matches!(edge.weight(), MessageOneOfEdge::OneOf(_)));

            if has_incoming_oneof && !has_outgoing_oneof {
                result.push(node);
            }
        }

        result.sort_unstable_by_key(|idx| idx.index());
        result
    }

    /// For each wrapped message node, walks upward through incoming `OneOf` edges.
    ///
    /// The traversal for one start node is cancelled if a node has more than one
    /// incoming edge, or if its single incoming edge is not `OneOf`.
    /// Parent re-encounter does not cancel the path; the walk stops after
    /// recording that step to avoid infinite loops.
    ///
    /// Each returned path carries:
    /// - node indices in both directions (`upward`/`downward`)
    /// - oneof edge payloads in both directions (`*_oneof_variants`)
    pub fn oneof_parent_paths_for_wrapped_messages(&self) -> Vec<MessageOneOfPath> {
        let mut paths = Vec::new();

        for start in self.message_wrapped_in_union_indices() {
            let mut upward = vec![start];
            let mut upward_oneof_variants = Vec::new();
            let mut current = start;
            let mut cancelled = false;

            loop {
                let incoming_edges: Vec<_> = self
                    .graph
                    .edges_directed(current, Direction::Incoming)
                    .collect();

                if incoming_edges.is_empty() {
                    break;
                }

                if incoming_edges.len() != 1 {
                    cancelled = true;
                    break;
                }

                let edge = incoming_edges[0];
                let MessageOneOfEdge::OneOf(oneof_name) = edge.weight() else {
                    cancelled = true;
                    break;
                };
                let parent = edge.source();
                upward.push(parent);
                upward_oneof_variants.push(oneof_name.clone());
                if upward[..upward.len() - 1].contains(&parent) {
                    break;
                }
                current = parent;
            }

            if !cancelled {
                let downward = upward.iter().rev().copied().collect();
                let downward_oneof_variants = upward_oneof_variants.iter().rev().cloned().collect();
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

    pub fn node_name(&self, node: NodeIndex) -> Option<&str> {
        self.graph.node_weight(node).map(String::as_str)
    }
}
