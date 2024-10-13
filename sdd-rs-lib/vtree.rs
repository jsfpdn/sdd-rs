use std::{cell::RefCell, fmt::Debug, rc::Rc};

use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::{Literal, VarLabel},
    manager::SddManager,
};

#[derive(Clone, PartialEq)]
pub(crate) enum Node {
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

#[derive(PartialEq)]
pub struct VTree {
    parent: Option<VTreeRef>,
    // Index according to the inorder traversal of the VTree. Can change when manipulating the tree in any way,
    // e.g. adding/removing variables and swapping or rotating nodes.
    idx: u16,
    node: Node,

    // Pointer to first vtree node in the subtree given by the current node
    // according to the inorder.
    inorder_first: Option<VTreeRef>,
    // Pointer to first vtree node in the subtree given by the current node
    // according to the inorder.
    inorder_last: Option<VTreeRef>,
    // TODO: Add pointer to the next vtree node according to inorder traversal.
}

impl Debug for VTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.node.clone() {
            Node::Leaf(label) => write!(f, "leaf {} for {}", self.idx, label.str()),
            Node::Internal(lc, rc) => write!(
                f,
                "internal {} ({}, {})",
                self.idx,
                lc.borrow().idx,
                rc.borrow().idx
            ),
        }
    }
}

impl VTree {
    #[must_use]
    pub(crate) fn new(parent: Option<VTreeRef>, idx: u16, node: Node) -> VTree {
        VTree {
            parent,
            idx,
            node,
            inorder_first: None,
            inorder_last: None,
        }
    }

    #[must_use]
    pub(crate) fn new_as_ref(parent: Option<VTreeRef>, idx: u16, node: Node) -> VTreeRef {
        Rc::new(RefCell::new(VTree::new(parent, idx, node)))
    }

    /// Sets the left child of this [`VTree`].
    ///
    /// # Panics
    ///
    /// Panics if the vtree does not represent an internal node.
    fn set_left_child(&mut self, left_child: &VTreeRef) {
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
    fn set_right_child(&mut self, right_child: &VTreeRef) {
        match self.node.clone() {
            Node::Leaf(_) => panic!("should not happen!"),
            Node::Internal(lc, _) => self.node = Node::Internal(lc, right_child.clone()),
        }
    }

    fn inorder_first_idx(&self) -> u16 {
        self.inorder_first.clone().unwrap().borrow().idx
    }

    fn inorder_last_idx(&self) -> u16 {
        self.inorder_last.clone().unwrap().borrow().idx
    }

    fn set_pointers(
        &mut self,
        inorder_first: Option<VTreeRef>,
        inorder_last: Option<VTreeRef>,
        idx: u16,
    ) {
        self.idx = idx;
        self.inorder_first = inorder_first;
        self.inorder_last = inorder_last;
    }
}

/// VTreeOrder describes the relation between two vtrees.
#[derive(Debug, PartialEq)]
pub(crate) enum VTreeOrder {
    // The two compared vtrees are one and the same.
    Equal,
    // The two compared vtrees are not subtress of one another.
    Inequal,
    // Left vtree is a sub-vtree of the right vtree.
    LeftSubOfRight,
    // Right vtree is a sub-vtree of the left vtree.
    RightSubOfLeft,
}

pub(crate) type VTreeRef = Rc<RefCell<VTree>>;

pub struct VTreeManager {
    root: Option<VTreeRef>,

    // TODO: Fix the meaningless bookkeeping and computation of
    // next_idx in `VTreeManager::add_variable`.
    next_idx: u16,
    // TODO: Change the Rc<RefCell<...>> approach to indexing into
    // global hashmap owning all the nodes.
    //
    // TODO: Hold index of the root and the first node in the inorder traversal.
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
    pub(crate) fn add_variable(&mut self, label: VarLabel) {
        let new_leaf = VTree::new_as_ref(None, self.next_idx, Node::Leaf(label));
        new_leaf.borrow_mut().inorder_last = Some(new_leaf.clone());

        if self.root.is_none() {
            self.next_idx += 1;
            self.root = Some(new_leaf);
            VTreeManager::set_inorder_indices(self.root.clone().unwrap(), 0);
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
                    rightest.borrow().parent.clone(),
                    self.next_idx,
                    Node::Internal(rightest.clone(), new_leaf.clone()),
                );
                self.next_idx += 1;

                rightest.borrow_mut().parent = Some(parent.clone());
                new_leaf.borrow_mut().parent = Some(parent.clone());

                match parent.borrow().parent.as_ref() {
                    None => self.root = Some(parent.clone()),
                    Some(p_parent) => p_parent.borrow_mut().set_right_child(&parent),
                };
            }
        }

        // TODO: This can be optimized further.
        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), 0);
    }

    fn set_inorder_indices(node: VTreeRef, idx: u16) -> (u16, Option<VTreeRef>, Option<VTreeRef>) {
        let (new_idx, par_idx, fst, last) =
            if let Node::Internal(lc, rc) = node.borrow().node.clone() {
                let (new_idx, fst, _) = VTreeManager::set_inorder_indices(lc, idx);
                let (par_idx, _, last) = VTreeManager::set_inorder_indices(rc, new_idx + 1);

                (new_idx, par_idx, fst, last)
            } else {
                (idx, idx + 1, Some(node.clone()), Some(node.clone()))
            };

        node.borrow_mut()
            .set_pointers(fst.clone(), last.clone(), new_idx);

        (par_idx, fst, last)
    }

    #[must_use]
    pub(crate) fn variables_total_order(&self) -> Vec<(VarLabel, u16)> {
        fn dfs(vtree: &VTreeRef, order: &mut Vec<(VarLabel, u16)>) {
            let idx = vtree.borrow().idx;
            match vtree.borrow().node.clone() {
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
        {
            // Set right child of `w` to `b`.
            let mut borrowed = vtree.borrow_mut();
            match borrowed.node.clone() {
                Node::Leaf(_) => panic!("cannot rotate leaf"),
                Node::Internal(lc, _) => borrowed
                    .parent
                    .clone()
                    .unwrap()
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

        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), 0);
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
        {
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

        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), 0);
    }

    /// Swaps children of internal node.
    ///
    /// # Panics
    ///
    /// Panics if called on a vtree representing a leaf node.
    pub fn swap(&mut self, vtree: &VTreeRef) {
        {
            let mut borrowed = vtree.borrow_mut();
            match &borrowed.node {
                Node::Leaf(_) => panic!("cannot swap children of a leaf node"),
                Node::Internal(lc, rc) => {
                    borrowed.node = Node::Internal(rc.clone(), lc.clone());
                }
            }
        }

        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), 0);
    }

    pub(crate) fn get_variable_vtree(&self, variable: &VarLabel) -> Option<VTreeRef> {
        fn find_vtree(vtree: &VTreeRef, variable: &VarLabel) -> Option<VTreeRef> {
            match vtree.borrow().node.clone() {
                Node::Internal(lc, rc) => find_vtree(&lc, variable)
                    .or(find_vtree(&rc, variable))
                    .or(None),
                Node::Leaf(candidate_variable) => {
                    if *variable == candidate_variable {
                        Some(vtree.clone())
                    } else {
                        None
                    }
                }
            }
        }

        find_vtree(&self.root.clone().unwrap(), variable)
    }

    fn get_vtree(&self, index: u16) -> Option<VTreeRef> {
        // TODO: This will get obsolete once VTrees are stored in a single hashmap.
        let Some(mut current) = self.root.clone() else {
            return None;
        };

        loop {
            let current_index = current.borrow().idx;
            if current_index == index {
                return Some(current);
            }

            if let Node::Internal(lc, rc) = current.clone().borrow().node.clone() {
                if index < current_index {
                    current = lc.clone();
                } else {
                    current = rc.clone();
                }
            }
        }
    }

    pub(crate) fn least_common_ancestor(
        &self,
        fst_idx: u16,
        snd_idx: u16,
    ) -> (VTreeRef, VTreeOrder) {
        assert!(
            fst_idx <= snd_idx,
            "`fst` must have index smaller than or greater to `snd`"
        );

        let fst = self
            .get_vtree(fst_idx)
            .expect(format!("vtree with index {} does not exist", fst_idx).as_str());
        let snd = self
            .get_vtree(snd_idx)
            .expect(format!("vtree with index {} does not exist", snd_idx).as_str());

        if fst_idx == snd_idx {
            return (fst.clone(), VTreeOrder::Equal);
        }

        if fst_idx >= snd.borrow().inorder_first_idx() {
            return (snd.clone(), VTreeOrder::LeftSubOfRight);
        }

        if snd_idx <= fst.borrow().inorder_last_idx() {
            return (fst.clone(), VTreeOrder::RightSubOfLeft);
        }

        let mut lca = fst.borrow().parent.clone().unwrap();
        while snd_idx > lca.borrow().inorder_last_idx() {
            lca = {
                let parent = lca.borrow().parent.clone().unwrap();
                parent
            }
        }

        (lca, VTreeOrder::Inequal)
    }
}

impl Dot for VTreeManager {
    fn draw(&self, writer: &mut DotWriter, _: &SddManager) {
        if self.root.is_none() {
            return;
        }

        // Get the total order first to neatly order the leaf nodes in the graph.
        for (label, idx) in self.variables_total_order() {
            writer.add_node(usize::from(idx), NodeType::CircleStr(label.str()));
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
                    usize::from(vtree.idx),
                    NodeType::Circle(u32::from(vtree.idx)),
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
    use crate::{
        literal::VarLabel,
        vtree::{Node, VTreeOrder, VTreeRef},
    };

    use super::VTreeManager;

    fn orders_eq(got_order: Vec<(VarLabel, u16)>, want_order: Vec<VarLabel>) {
        assert_eq!(got_order.len(), want_order.len());
        for ((got, _), want) in got_order.iter().zip(want_order) {
            assert_eq!(got, &want);
        }
    }

    #[allow(unused)]
    fn left_child(vtree: &VTreeRef) -> VTreeRef {
        match vtree.borrow().node.clone() {
            Node::Leaf(_) => panic!("vtree node is a leaf instead of internal node"),
            Node::Internal(lc, _) => lc,
        }
    }

    fn right_child(vtree: &VTreeRef) -> VTreeRef {
        match vtree.borrow().node.clone() {
            Node::Leaf(_) => panic!("vtree node is a leaf instead of internal node"),
            Node::Internal(_, rc) => rc,
        }
    }

    #[test]
    fn inorder_traversal() {
        // Helper functions to retrieve indices of first and last nodes according
        // to the inorder in a given sub-vtree.
        let get_inorder_first =
            |vref: VTreeRef| vref.borrow().inorder_first.clone().unwrap().borrow().idx;
        let get_inorder_last =
            |vref: VTreeRef| vref.borrow().inorder_last.clone().unwrap().borrow().idx;

        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));
        manager.add_variable(VarLabel::new("C"));
        manager.add_variable(VarLabel::new("D"));

        // Rotate the right child of root to the left to make the tree balanced as in the diagram.
        let Node::Internal(_, rc) = manager
            .root
            .as_ref()
            .expect("must have a root")
            .borrow()
            .node
            .clone()
        else {
            panic!("root must be an internal node, not a leaf")
        };

        manager.rotate_left(&rc);

        let root = manager.root.unwrap().clone();
        assert_eq!(root.borrow().idx, 3);
        assert_eq!(get_inorder_first(root.clone()), 0);
        assert_eq!(get_inorder_last(root.clone()), 6);

        let Node::Internal(lc, rc) = root.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };

        assert_eq!(lc.borrow().idx, 1);
        assert_eq!(get_inorder_first(lc.clone()), 0);
        assert_eq!(get_inorder_last(lc.clone()), 2);

        assert_eq!(rc.borrow().idx, 5);
        assert_eq!(get_inorder_first(rc.clone()), 4);
        assert_eq!(get_inorder_last(rc.clone()), 6);

        let Node::Internal(llc, lrc) = lc.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };
        assert_eq!(llc.borrow().idx, 0);
        assert_eq!(get_inorder_first(llc.clone()), 0);
        assert_eq!(get_inorder_last(llc.clone()), 0);

        assert_eq!(lrc.borrow().idx, 2);
        assert_eq!(get_inorder_first(lrc.clone()), 2);
        assert_eq!(get_inorder_last(lrc.clone()), 2);

        let Node::Internal(rlc, rrc) = rc.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };
        assert_eq!(rlc.borrow().idx, 4);
        assert_eq!(get_inorder_first(rlc.clone()), 4);
        assert_eq!(get_inorder_last(rlc.clone()), 4);

        assert_eq!(rrc.borrow().idx, 6);
        assert_eq!(get_inorder_first(rrc.clone()), 6);
        assert_eq!(get_inorder_last(rrc.clone()), 6);
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
        if let Node::Internal(lc, rc) = manager.root.unwrap().borrow().node.clone() {
            let a = lc.borrow().node.clone();
            assert!(matches!(a, Node::Leaf(label) if label.eq(&VarLabel::new("A"))));

            let inner = rc.borrow().node.clone();
            match inner {
                Node::Leaf(_) => panic!("Node should've been internal"),
                Node::Internal(lc, rc) => {
                    let b = lc.borrow().node.clone();
                    let c = rc.borrow().node.clone();

                    assert!(matches!(b, Node::Leaf(label) if label.eq(&VarLabel::new("B"))));
                    assert!(matches!(c, Node::Leaf(label) if label.eq(&VarLabel::new("C"))));
                }
            }
        }
    }

    #[test]
    fn variables_total_order_simple() {
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));
        manager.add_variable(VarLabel::new("C"));

        let want_order = vec![VarLabel::new("A"), VarLabel::new("B"), VarLabel::new("C")];
        orders_eq(manager.variables_total_order(), want_order);
    }

    #[test]
    fn variables_total_order_swap() {
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));

        let root = manager.root.clone().unwrap();

        // <A, B> ~> <B, A>
        manager.swap(&root);
        orders_eq(
            manager.variables_total_order(),
            vec![VarLabel::new("B"), VarLabel::new("A")],
        );

        // <B, A> ~> <A, B>
        manager.swap(&root);
        orders_eq(
            manager.variables_total_order(),
            vec![VarLabel::new("A"), VarLabel::new("B")],
        );
    }

    #[test]
    fn variables_total_order() {
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

        let x = manager.root.clone().unwrap().borrow().node.clone();

        let rc = match x {
            Node::Leaf(_) => panic!("cannot happen"),
            Node::Internal(_, rc) => rc,
        };

        manager.rotate_left(&rc);

        // The total order must not change when rotating.
        orders_eq(manager.variables_total_order(), want_order.clone());

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
        orders_eq(manager.variables_total_order(), want_order.clone());

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

    #[test]
    fn least_common_ancestor() {
        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));
        manager.add_variable(VarLabel::new("C"));
        manager.add_variable(VarLabel::new("D"));
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        // Rotate the right child of root to the left to make the tree balanced as in the diagram above.
        let root = manager.root.clone().unwrap();
        manager.rotate_left(&right_child(&root));

        let root = manager.root.clone().unwrap();
        let root_idx = root.borrow().idx;

        // root has index of 3
        let (lca, ord) = manager.least_common_ancestor(root_idx, root_idx);
        assert_eq!(ord, VTreeOrder::Equal);
        assert_eq!(lca.borrow().idx, root_idx);

        // lc has index of 1
        let (lca, ord) = manager.least_common_ancestor(1, root_idx);
        assert_eq!(ord, VTreeOrder::LeftSubOfRight);
        assert_eq!(lca.borrow().idx, root_idx);

        // rc has index of 5
        let (lca, ord) = manager.least_common_ancestor(root_idx, 5);
        assert_eq!(ord, VTreeOrder::RightSubOfLeft);
        assert_eq!(lca.borrow().idx, root_idx);

        // llc has index of 0, rrc has index of 6
        let (lca, ord) = manager.least_common_ancestor(0, 6);
        assert_eq!(ord, VTreeOrder::Inequal);
        assert_eq!(lca.borrow().idx, root_idx);
    }

    #[test]
    fn literal_indices() {
        let var_label_index = |vtree: Option<VTreeRef>| -> u16 { vtree.unwrap().borrow().idx };

        let mut manager = VTreeManager::new();
        manager.add_variable(VarLabel::new("A"));
        manager.add_variable(VarLabel::new("B"));
        manager.add_variable(VarLabel::new("C"));
        manager.add_variable(VarLabel::new("D"));
        //     1
        //   /   \
        //  0     3
        //  A   /   \
        //     2     5
        //     B   /   \
        //        4     6
        //        C     D

        assert_eq!(
            var_label_index(manager.get_variable_vtree(&VarLabel::new("A"))),
            0
        );
        assert_eq!(
            var_label_index(manager.get_variable_vtree(&VarLabel::new("B"))),
            2
        );
        assert_eq!(
            var_label_index(manager.get_variable_vtree(&VarLabel::new("C"))),
            4
        );
        assert_eq!(
            var_label_index(manager.get_variable_vtree(&VarLabel::new("D"))),
            6
        );
        assert_eq!(manager.get_variable_vtree(&VarLabel::new("E")), None);
    }
}
