use crate::{manager::SddManager, Result};

pub trait Dot {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager);
}

pub enum Edge {
    Simple(usize, usize),
    Prime(usize, usize),
    Sub(usize, usize),
}

impl std::fmt::Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Edge::Simple(from, to) => write!(f, "{from} -> {to}"),
            Edge::Prime(from, to) => write!(f, "{from}:f0 -> {to}"),
            Edge::Sub(from, to) => write!(f, "{from}:f1 -> {to}"),
        }
    }
}

#[derive(Default)]
pub struct DotWriter {
    graph_name: String,

    nodes: Vec<(usize, NodeType)>,
    edges: Vec<Edge>,
}

pub enum NodeType {
    Box(String),
    Circle(u32),
    CircleStr(String),
    Record(String, String),
}

impl NodeType {
    fn shape(&self) -> String {
        let shape_type = match self {
            NodeType::Box(_) => "box",
            NodeType::Record(_, _) => "record",
            NodeType::Circle(_) | NodeType::CircleStr(_) => "circle",
        }
        .to_owned();

        format!("shape={shape_type}")
    }

    fn label(&self) -> String {
        match self {
            NodeType::Record(fst, snd) => format!("label=\"<f0> {fst} | <f1> {snd}\""),
            NodeType::Circle(label) => format!("label=\"{label}\""),
            NodeType::CircleStr(label) => format!("label=\"{label}\""),
            NodeType::Box(_) => String::new(),
        }
    }

    fn metadata() -> String {
        "height=.25 width=.2".to_owned()
    }
}

impl DotWriter {
    #[must_use]
    pub fn new(graph_name: String) -> DotWriter {
        DotWriter {
            graph_name,
            ..Default::default()
        }
    }

    pub fn add_node(&mut self, node_idx: usize, node_type: NodeType) {
        self.nodes.push((node_idx, node_type));
    }

    pub fn add_edge(&mut self, edge: Edge) {
        self.edges.push(edge);
    }

    /// # Errors
    /// Function returns an error if the writing to a file or flushing fails.
    pub fn write(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        write!(writer, "digraph {} {{\n  overlap=false", self.graph_name)?;

        for (node, node_type) in &self.nodes {
            write!(
                writer,
                "\n  {node} [{} {} {}]",
                node_type.shape(),
                node_type.label(),
                NodeType::metadata(),
            )?;
        }

        for edge in &self.edges {
            // TODO: Make the edge begin in the middle of the child.
            write!(writer, "\n  {edge} [arrowsize=.50]")?;
        }

        write!(writer, "\n}}")?;
        writer.flush()?;
        Ok(())
    }
}
