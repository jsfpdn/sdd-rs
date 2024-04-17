use std::{cell::RefCell, fmt::Debug, rc::Rc};

use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::VarLabel,
};

#[derive(Clone)]
pub enum Node {
    Leaf(VarLabel),
    Internal(VTreeRef, VTreeRef),
}

impl Node {
    #[must_use]
    pub fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf(_))
    }

    #[must_use]
    pub fn is_internal(&self) -> bool {
        !self.is_leaf()
    }
}

pub struct VTree {
    parent: Option<VTreeRef>,
    idx: u16,
    node: Node,
}

impl Debug for VTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.node.clone() {
            Node::Leaf(label) => write!(f, "leaf {} for {}", self.idx, label.str()),
            Node::Internal(lc, rc) => write!(
                f,
                "internal {} ({}, {})",
                self.idx,
                lc.as_ref().borrow().idx,
                rc.as_ref().borrow().idx
            ),
        }
    }
}

impl VTree {
    #[must_use]
    pub fn new(parent: Option<VTreeRef>, idx: u16, node: Node) -> VTree {
        VTree { parent, idx, node }
    }

    #[must_use]
    pub fn new_as_ref(parent: Option<VTreeRef>, idx: u16, node: Node) -> VTreeRef {
        Rc::new(RefCell::new(VTree::new(parent, idx, node)))
    }

    /// Sets the left child of this [`VTree`].
    ///
    /// # Panics
    ///
    /// Panics if the vtree does not represent an internal node.
    pub fn set_left_child(&mut self, left_child: &VTreeRef) {
        match self.node.clone() {
            Node::Leaf(_) => panic!("should not happen!"),
            Node::Internal(_, rc) => self.node = Node::Internal(left_child.clone(), rc),
        }
    }

    /// Sets the right child of this [`VTree`].
    ///
    /// # Panics
    ///
    /// Panics if the vtree does not represent an internal node.
    pub fn set_right_child(&mut self, right_child: &VTreeRef) {
        match self.node.clone() {
            Node::Leaf(_) => panic!("should not happen!"),
            Node::Internal(lc, _) => self.node = Node::Internal(lc, right_child.clone()),
        }
    }
}

pub type VTreeRef = Rc<RefCell<VTree>>;

impl VTree {
    //       w
    //      / \
    //     a   x
    //        / \
    //       b   c
    //
    //  rotate_left(x):
    //
    //       x
    //      / \
    //     w   c
    //    / \
    //   a   b
    //
    pub fn rotate_left(&mut self) {
        // self.left.parent = self.parent
        // self.parent.right = self.left
        // self.left = self.parent
        unimplemented!("TBD")
    }

    pub fn rotate_right(&mut self) {
        unimplemented!("TBD")
    }

    /// Swaps children of in internal node.
    ///
    /// # Panics
    ///
    /// Panics if called on a vtree representing a leaf node.
    pub fn swap(&mut self) {
        match self.node.clone() {
            Node::Leaf(_) => panic!("cannot swap children of a leaf node"),
            Node::Internal(lc, rc) => {
                self.node = Node::Internal(rc, lc);
            }
        }
    }
}

pub struct VTreeManager {
    root: Option<VTreeRef>,

    next_idx: u16,
}

impl VTreeManager {
    #[must_use]
    pub fn new() -> VTreeManager {
        VTreeManager {
            root: None,
            next_idx: 0,
        }
    }

    /// Add variable to the variable tree. The variable is inserted to the very end of the total
    /// variable order.
    pub fn add_variable(&mut self, label: VarLabel) {
        let new_leaf = VTree::new_as_ref(None, self.next_idx, Node::Leaf(label));
        self.next_idx += 1;

        if self.root.is_none() {
            self.root = Some(new_leaf);
            return;
        }

        match self.root.as_ref() {
            None => self.root = Some(new_leaf),
            Some(rightest) => {
                // Add the new variable to the end of the rightest path of the tree.
                let mut rightest = rightest.clone();
                loop {
                    let tmp = match rightest.borrow().node.clone() {
                        Node::Leaf(_) => break,
                        Node::Internal(_, right_child) => right_child.clone(),
                    };

                    rightest = tmp;
                }

                let parent = VTree::new_as_ref(
                    rightest.as_ref().borrow().parent.clone(),
                    self.next_idx,
                    Node::Internal(rightest.clone(), new_leaf.clone()),
                );
                self.next_idx += 1;

                rightest.as_ref().borrow_mut().parent = Some(parent.clone());
                new_leaf.as_ref().borrow_mut().parent = Some(parent.clone());

                match parent.borrow().parent.as_ref() {
                    None => self.root = Some(parent.clone()),
                    Some(p_parent) => p_parent.as_ref().borrow_mut().set_right_child(&parent),
                };
            }
        }
    }

    #[must_use]
    pub fn total_order(&self) -> Vec<(VarLabel, u16)> {
        fn dfs(vtree: &VTreeRef, order: &mut Vec<(VarLabel, u16)>) {
            let idx = vtree.as_ref().borrow().idx;
            match vtree.as_ref().borrow().node.clone() {
                Node::Leaf(label) => order.push((label, idx)),
                Node::Internal(lc, rc) => {
                    dfs(&lc, order);
                    dfs(&rc, order);
                }
            }
        }

        let mut order = Vec::new();
        if let Some(root) = self.root.as_ref() {
            dfs(root, &mut order);
        }

        order
    }
}

impl Dot for VTreeManager {
    fn draw(&self, writer: &mut DotWriter) {
        if self.root.is_none() {
            return;
        }

        // Get the total order first to neatly order the leaf nodes in the graph.
        for (label, idx) in self.total_order() {
            writer.add_node(
                usize::try_from(idx).unwrap(),
                NodeType::CircleStr(label.str()),
            );
        }

        let mut nodes = vec![self.root.as_ref().unwrap().clone()];
        while let Some(vtree) = nodes.pop() {
            let vtree = vtree.borrow();
            if let Node::Internal(lc, rc) = vtree.node.clone() {
                writer.add_edge(Edge::Simple(vtree.idx as usize, lc.borrow().idx as usize));
                writer.add_edge(Edge::Simple(vtree.idx as usize, rc.borrow().idx as usize));
                nodes.push(lc.clone());
                nodes.push(rc.clone());

                writer.add_node(
                    usize::try_from(vtree.idx).unwrap(),
                    NodeType::Circle(u32::try_from(vtree.idx).unwrap()),
                );
            };
        }
    }
}

impl Default for VTreeManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use crate::{literal::VarLabel, vtree::Node};

    use super::VTreeManager;

    fn orders_eq(got_order: Vec<(VarLabel, u16)>, want_order: Vec<VarLabel>) {
        assert_eq!(got_order.len(), want_order.len());
        println!("want: {:?}, got: {:?}", want_order, got_order);
        for ((got, _), want) in got_order.iter().zip(want_order) {
            assert_eq!(got, &want);
        }
    }

    #[test]
    fn structure() {
        let mut manager = VTreeManager::new();
        assert!(manager.root.is_none());

        manager.add_variable(VarLabel::new("A"));
        assert!(manager.root.is_some());
        assert!(manager
            .root
            .clone()
            .is_some_and(|root| root.as_ref().borrow().node.is_leaf()));

        manager.add_variable(VarLabel::new("B"));
        assert!(manager
            .root
            .clone()
            .is_some_and(|root| root.as_ref().borrow().node.is_internal()));

        manager.add_variable(VarLabel::new("C"));

        // Test that the vtree has the following structure:
        //    *
        //   / \
        //  A   *
        //     / \
        //    B   C
        if let Node::Internal(lc, rc) = manager.root.unwrap().as_ref().borrow().node.clone() {
            let a = lc.as_ref().borrow().node.clone();
            assert!(matches!(a, Node::Leaf(label) if label.eq(&VarLabel::new("A"))));

            let inner = rc.as_ref().borrow().node.clone();
            match inner {
                Node::Leaf(_) => panic!("Node should've been internal"),
                Node::Internal(lc, rc) => {
                    let b = lc.as_ref().borrow().node.clone();
                    let c = rc.as_ref().borrow().node.clone();

                    assert!(matches!(b, Node::Leaf(label) if label.eq(&VarLabel::new("B"))));
                    assert!(matches!(c, Node::Leaf(label) if label.eq(&VarLabel::new("C"))));
                }
            }
        }
    }

    #[test]
    fn total_order() {
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));
        manager.add_variable(VarLabel::new("C"));

        let want_order = vec![VarLabel::new("A"), VarLabel::new("B"), VarLabel::new("C")];
        orders_eq(manager.total_order(), want_order);
    }

    #[test]
    fn swap() {
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));

        // <A, B> ~> <B, A>
        manager.root.clone().unwrap().as_ref().borrow_mut().swap();
        orders_eq(
            manager.total_order(),
            vec![VarLabel::new("B"), VarLabel::new("A")],
        );

        // <B, A> ~> <A, B>
        manager.root.clone().unwrap().as_ref().borrow_mut().swap();
        orders_eq(
            manager.total_order(),
            vec![VarLabel::new("A"), VarLabel::new("B")],
        );
    }
}
