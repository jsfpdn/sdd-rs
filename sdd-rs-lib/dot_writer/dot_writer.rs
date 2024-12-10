pub trait Dot {
    fn draw(&self, writer: &mut DotWriter);
}

#[derive(PartialEq)]
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

/// [`DotWriter`] is responsible for drawing SDDs and vtrees
/// in the .DOT Graphviz format.
#[derive(Default)]
pub struct DotWriter {
    graph_name: String,
    show_ids: bool,

    nodes: Vec<(usize, NodeType)>,
    edges: Vec<Edge>,
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

    pub(crate) fn add_edge(&mut self, edge: Edge) {
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
    pub(crate) fn write(&self, writer: &mut dyn std::io::Write) -> Result<(), String> {
        write!(
            writer,
            "digraph {} {{\n  overlap=false\n  ordering=out",
            self.graph_name
        )
        .map_err(|err| err.to_string())?;

        for (node, node_type) in &self.nodes {
            write!(
                writer,
                "\n  {node} [{} {} {}]",
                node_type.shape(),
                node_type.label(self.show_ids),
                NodeType::metadata(),
            )
            .map_err(|err| err.to_string())?;
        }

        for edge in &self.edges {
            // TODO: Make the edge begin in the middle of the child.
            write!(writer, "\n  {edge} [arrowsize=.50]").map_err(|err| err.to_string())?;
        }

        write!(writer, "\n}}").map_err(|err| err.to_string())?;
        writer.flush().map_err(|err| err.to_string())?;
        Ok(())
    }
}
