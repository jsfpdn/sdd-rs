use anyhow::Result;

pub trait Dot {
    fn draw(&self, writer: &mut DotWriter);
}

#[derive(PartialEq)]
pub enum EdgeType {
    Simple(usize, usize),
    Prime(usize, usize),
    Sub(usize, usize),
}

impl std::fmt::Display for EdgeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EdgeType::Simple(from, to) => write!(f, "{from} -> {to}"),
            EdgeType::Prime(from, to) => write!(f, "{from}:f0 -> {to}"),
            EdgeType::Sub(from, to) => write!(f, "{from}:f1 -> {to}"),
        }
    }
}

/// [`DotWriter`] is responsible for drawing SDDs and vtrees
/// in the .DOT Graphviz format.
#[derive(Default)]
pub struct DotWriter {
    graph_name: String,
    show_ids: bool,

    nodes: Vec<(usize, NodeType)>,
    edges: Vec<EdgeType>,
}

#[derive(Debug)]
pub(crate) enum NodeType {
    Circle(String, Option<usize>),
    Record(String, String),
}

impl NodeType {
    fn shape(&self) -> String {
        let shape_type = match self {
            // NodeType::Box(_) => "box",
            NodeType::Record(_, _) => "record",
            NodeType::Circle(_, _) => "circle",
        }
        .to_owned();

        format!("shape={shape_type}")
    }

    fn label(&self, verbose: bool) -> String {
        match self {
            NodeType::Record(fst, snd) => format!("label=\"<f0> {fst} | <f1> {snd}\""),
            NodeType::Circle(label, Some(idx)) if verbose => {
                format!("label=<{label}>, xlabel=<<FONT POINT-SIZE=\"7\">{idx}</FONT>>, fillcolor=white, style=filled")
            }
            NodeType::Circle(label, _) => format!("label=<{label}>"),
        }
    }

    fn metadata() -> String {
        "height=.25 width=.2".to_owned()
    }
}

impl DotWriter {
    #[must_use]
    pub(crate) fn new(graph_name: String, show_ids: bool) -> DotWriter {
        DotWriter {
            graph_name,
            show_ids,
            ..Default::default()
        }
    }

    pub(crate) fn add_node(&mut self, node_idx: usize, node_type: NodeType) {
        self.nodes.push((node_idx, node_type));
    }

    pub(crate) fn add_edge(&mut self, edge: EdgeType) {
        for other in &self.edges {
            if *other == edge {
                // We have already added this edge.
                return;
            }
        }

        self.edges.push(edge);
    }

    /// # Errors
    /// Function returns an error if the writing to a file or flushing fails.
    pub(crate) fn write(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        write!(
            writer,
            "digraph {} {{\n  overlap=false\n  ordering=out",
            self.graph_name
        )?;

        for (node, node_type) in &self.nodes {
            write!(
                writer,
                "\n  {node} [{} {} {}]",
                node_type.shape(),
                node_type.label(self.show_ids),
                NodeType::metadata(),
            )?;
        }

        // TODO: Make the edge begin in the middle of the child.
        for edge in &self.edges {
            write!(writer, "\n  {edge} [arrowsize=.50]")?;
        }

        write!(writer, "\n}}")?;
        writer.flush()?;
        Ok(())
    }
}
