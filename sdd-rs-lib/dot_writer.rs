use crate::manager::Result;

pub trait Dot {
    fn draw(&self, writer: &mut DotWriter);
}

#[derive(Default)]
pub struct DotWriter {
    nodes: Vec<(usize, NodeType)>,
    edges: Vec<((usize, Option<usize>), usize)>,
}

pub enum NodeType {
    Box(String),
    Circle(u32),
    Record(String, String),
}

impl NodeType {
    fn shape(&self) -> String {
        let shape_type = match self {
            NodeType::Box(_) => "box",
            NodeType::Record(_, _) => "record",
            NodeType::Circle(_) => "circle",
        }
        .to_owned();

        format!("shape={shape_type}")
    }

    fn label(&self) -> String {
        match self {
            NodeType::Record(fst, snd) => format!("label=\"<f0> {fst} | <f1> {snd}\""),
            NodeType::Circle(label) => format!("label=\"{label}\""),
            NodeType::Box(_) => String::new(),
        }
    }

    fn metadata() -> String {
        "height=.25 width=.2".to_owned()
    }
}

impl DotWriter {
    #[must_use]
    pub fn new() -> DotWriter {
        DotWriter::default()
    }

    pub fn add_node(&mut self, node_idx: usize, node_type: NodeType) {
        self.nodes.push((node_idx, node_type));
    }

    pub fn add_edge(&mut self, from: (usize, Option<usize>), to: usize) {
        self.edges.push((from, to));
    }

    /// # Errors
    /// Function returns an error if the writing to a file or flushing fails.
    pub fn write(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        write!(writer, "digraph sdd {{\n  overlap=false")?;

        for (node, node_type) in &self.nodes {
            write!(
                writer,
                "\n  {} [{} {} {}]",
                node,
                node_type.shape(),
                node_type.label(),
                NodeType::metadata(),
            )?;
        }

        for ((from, from_child), to) in &self.edges {
            if let Some(from_child) = from_child {
                // TODO: Make the edge begin in the middle of the child.
                write!(writer, "\n  {from}:f{from_child} -> {to} [arrowsize=.50]")?;
            } else {
                write!(writer, "\n  {from} -> {to} [arrowsize=.50]")?;
            }
        }

        write!(writer, "\n}}")?;
        writer.flush()?;
        Ok(())
    }
}
