use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::VarLabel,
};

// TODO: Check 'Art of Computer Programming, Volume 4, Fascicle 4: Generating all Tree'

#[derive(PartialEq, Eq, Clone)]
pub enum VTree {
    Leaf(VarLabel),
    Node(Box<VTree>, Box<VTree>),
}

impl VTree {
    #[must_use]
    pub fn is_leaf(&self) -> bool {
        matches!(self, VTree::Leaf(_))
    }

    #[must_use]
    pub fn is_internal(&self) -> bool {
        !self.is_leaf()
    }
}

pub struct VTreeManager {
    nodes: Vec<VTree>,

    #[allow(dead_code)]
    /// DFS preorder traversal indexing to BFS indexing.
    dfs_to_bfs: Vec<usize>,

    #[allow(dead_code)]
    /// BFS indexing to DFS preorder traversal indexing.
    bfs_to_dfs: Vec<usize>,
}

// DFS preorder traversal:
//        0
//     1     4
//   2   3 5   6
//
// BFS:
//        0
//     1     2
//   3   4 5   6
//
// dfs_to_bfs: [0, 1, 3, 4, 2, 5, 6]
// bfs_to_dfs: [0, 1, 4, 2, 3, 5, 6]

impl VTreeManager {
    #[must_use]
    pub fn new(vtree: Option<VTree>) -> VTreeManager {
        VTreeManager {
            dfs_to_bfs: Vec::new(),
            bfs_to_dfs: Vec::new(),
            nodes: if let Some(root) = vtree {
                VTreeManager::discover_nodes(root)
            } else {
                Vec::new()
            },
        }
    }

    // pub fn add_variable(&mut self, _var_label: VarLabel) {
    //     // TODO: Where to put the new leaf?
    //     unimplemented!("TBD")
    // }

    fn discover_nodes(vtree: VTree) -> Vec<VTree> {
        let mut nodes = Vec::new();

        let mut q = vec![vtree];
        while let Some(v) = q.pop() {
            nodes.push(v.clone());
            if let VTree::Node(left, right) = v {
                q.push(left.as_ref().clone());
                q.push(right.as_ref().clone());
            }
        }

        nodes
    }

    // TODO: Implement dfs_to_bfs and bfs_to_dfs.
    // fn dfs_to_bfs(&self) {}
    // fn bfs_to_dfs(&self) {}
}

impl Dot for VTreeManager {
    fn draw(&self, writer: &mut DotWriter) {
        for (idx, node) in self.nodes.iter().enumerate() {
            let node_type = match node {
                VTree::Leaf(var_label) => NodeType::CircleStr(var_label.str()),
                VTree::Node(left, right) => {
                    let l_idx = self.nodes.iter().position(|l_c| l_c.eq(left)).unwrap();
                    let r_idx = self.nodes.iter().position(|r_c| r_c.eq(right)).unwrap();
                    writer.add_edge(Edge::Simple(idx, l_idx));
                    writer.add_edge(Edge::Simple(idx, r_idx));

                    NodeType::Circle(u32::try_from(idx).unwrap())
                }
            };

            writer.add_node(idx, node_type);
        }
    }
}

impl Default for VTreeManager {
    fn default() -> Self {
        Self::new(None)
    }
}
