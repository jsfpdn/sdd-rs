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

    /// Rotates the vtree to the left. Given the following tree,
    ///
    /// ```ignore
    ///       w
    ///      / \
    ///     a   x
    ///        / \
    ///       b   c
    /// ```
    ///
    /// `rotate_left(x)` will mutate the tree as follows:
    ///
    /// ```ignore
    ///       x
    ///      / \
    ///     w   c
    ///    / \
    ///   a   b
    /// ```
    /// # Panics
    ///
    /// Panics if called on a vtree that cannot be rotated.
    pub fn rotate_left(&mut self, vtree: &VTreeRef) {
        // Set right child of `w` to `b`.
        let mut borrowed = vtree.borrow_mut();
        match borrowed.node.clone() {
            Node::Leaf(_) => panic!("cannot rotate leaf"),
            Node::Internal(lc, _) => borrowed
                .parent
                .clone()
                .unwrap()
                .as_ref()
                .borrow_mut()
                .set_right_child(&lc),
        }

        // Set left child of `x` to `w`.
        let parent = borrowed.parent.clone().unwrap();
        borrowed.set_left_child(&parent);

        // Set parent of `x` to the parent of `w`.
        borrowed.parent = parent.borrow().parent.clone();
        if borrowed.parent.is_none() {
            // Set it as the root.
            self.root = Some(vtree.clone());
        }

        // Set parent of `w` to `x`.
        parent.borrow_mut().parent = Some(vtree.clone());
    }

    /// Rotates the vtree to the right. Given the following tree,
    ///
    /// ```ignore
    ///       w
    ///      / \
    ///     x   c
    ///    / \
    ///   a   b
    /// ```
    ///
    /// `rotate_right(x)` will mutate the tree as follows:
    ///
    /// ```ignore
    ///      x
    ///     / \
    ///    a   w
    ///       / \
    ///      b   c
    /// ```
    /// # Panics
    ///
    /// Panics if called on a vtree that cannot be rotated.
    pub fn rotate_right(&mut self, vtree: &VTreeRef) {
        // Set left child of `w` to `b`.
        let mut borrowed = vtree.borrow_mut();
        match borrowed.node.clone() {
            Node::Leaf(_) => panic!("cannot rotate leaf"),
            Node::Internal(_, rc) => borrowed
                .parent
                .clone()
                .unwrap()
                .borrow_mut()
                .set_left_child(&rc),
        }

        // Set right child of `x` to `w`.
        let parent = borrowed.parent.clone().unwrap();
        borrowed.set_right_child(&parent);

        // Set parent of `x` to the parent of `w`.
        borrowed.parent = parent.borrow().parent.clone();
        if borrowed.parent.is_none() {
            // `w` was the root therefore make `x` the new root.
            self.root = Some(vtree.clone());
        }

        // Set parent of `w` to `x`.
        parent.borrow_mut().parent = Some(vtree.clone());
    }

    /// Swaps children of in internal node.
    ///
    /// # Panics
    ///
    /// Panics if called on a vtree representing a leaf node.
    pub fn swap(&mut self, vtree: &VTreeRef) {
        let mut borrowed = vtree.borrow_mut();
        match &borrowed.node {
            Node::Leaf(_) => panic!("cannot swap children of a leaf node"),
            Node::Internal(lc, rc) => {
                borrowed.node = Node::Internal(rc.clone(), lc.clone());
            }
        }
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

        let root = manager.root.clone().unwrap();

        // <A, B> ~> <B, A>
        manager.swap(&root);
        orders_eq(
            manager.total_order(),
            vec![VarLabel::new("B"), VarLabel::new("A")],
        );

        // <B, A> ~> <A, B>
        manager.swap(&root);
        orders_eq(
            manager.total_order(),
            vec![VarLabel::new("A"), VarLabel::new("B")],
        );
    }

    #[test]
    fn rotate() {
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));
        manager.add_variable(VarLabel::new("C"));
        let want_order = vec![VarLabel::new("A"), VarLabel::new("B"), VarLabel::new("C")];

        // The tree intially looks like this:
        //    x
        //   / \
        //  A   y
        //     / \
        //    B   C

        let x = manager.root.clone().unwrap().as_ref().borrow().node.clone();

        let rc = match x {
            Node::Leaf(_) => panic!("cannot happen"),
            Node::Internal(_, rc) => rc,
        };

        manager.rotate_left(&rc);

        // The total order must not change when rotating.
        orders_eq(manager.total_order(), want_order.clone());

        // The tree must look like this:
        //     y
        //    / \
        //   x   C
        //  / \
        // A   B

        let y = manager.root.as_ref().unwrap().borrow().node.clone();
        let x = match y {
            Node::Leaf(_) => panic!("root cannot be currently a leaf"),
            Node::Internal(lc, rc) => {
                let c = rc.borrow().node.clone();

                assert!(matches!(c, Node::Leaf(label) if label.eq(&VarLabel::new("C"))));

                lc.clone()
            }
        };

        match x.borrow().node.clone() {
            Node::Leaf(_) => panic!("this should've been an internal node"),
            Node::Internal(lc, rc) => {
                let a = lc.borrow().node.clone();
                let b = rc.borrow().node.clone();

                assert!(matches!(a, Node::Leaf(label) if label.eq(&VarLabel::new("A"))));
                assert!(matches!(b, Node::Leaf(label) if label.eq(&VarLabel::new("B"))));
            }
        };

        manager.rotate_right(&x);

        // The total order must not change when rotating.
        orders_eq(manager.total_order(), want_order.clone());

        // The tree should like exactly like in the beginning:
        //    x
        //   / \
        //  A   y
        //     / \
        //    B   C

        let x = manager.root.as_ref().unwrap().borrow().node.clone();
        let y = match x {
            Node::Leaf(_) => panic!("root cannot be currently a leaf"),
            Node::Internal(lc, rc) => {
                let a = lc.borrow().node.clone();

                assert!(matches!(a, Node::Leaf(label) if label.eq(&VarLabel::new("A"))));

                rc.clone()
            }
        };

        match y.borrow().node.clone() {
            Node::Leaf(_) => panic!("this should've been an internal node"),
            Node::Internal(lc, rc) => {
                let b = lc.borrow().node.clone();
                let c = rc.borrow().node.clone();

                assert!(matches!(b, Node::Leaf(label) if label.eq(&VarLabel::new("B"))));
                assert!(matches!(c, Node::Leaf(label) if label.eq(&VarLabel::new("C"))));
            }
        };
    }
}
