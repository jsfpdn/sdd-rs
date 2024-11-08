use std::{
    cell::RefCell,
    collections::BTreeSet,
    fmt::{Debug, Display},
    ops::{Add, AddAssign, Sub},
    rc::Rc,
};

use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    literal::Variable,
    manager::SddManager,
};

#[derive(Clone, PartialEq)]
pub(super) enum Node {
    Leaf(Variable),
    Internal(VTreeRef, VTreeRef),
}

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug, Copy)]
pub struct VTreeIdx(pub u32);

impl Add for VTreeIdx {
    type Output = VTreeIdx;

    fn add(self, rhs: Self) -> Self::Output {
        VTreeIdx(self.0 + rhs.0)
    }
}

impl Sub for VTreeIdx {
    type Output = VTreeIdx;

    fn sub(self, rhs: Self) -> Self::Output {
        VTreeIdx(self.0 - rhs.0)
    }
}

impl AddAssign for VTreeIdx {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0;
    }
}

impl Display for VTreeIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<u16> for VTreeIdx {
    fn from(value: u16) -> Self {
        VTreeIdx(value as u32)
    }
}

impl From<u32> for VTreeIdx {
    fn from(value: u32) -> Self {
        VTreeIdx(value)
    }
}

impl From<usize> for VTreeIdx {
    fn from(value: usize) -> Self {
        VTreeIdx(value.try_into().unwrap())
    }
}

#[derive(PartialEq)]
pub struct VTree {
    parent: Option<VTreeRef>,
    // Index according to the inorder traversal of the VTree. Can change when manipulating the tree in any way,
    // e.g. adding/removing variables and swapping or rotating nodes.
    idx: VTreeIdx,

    pub(super) node: Node,

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
            Node::Leaf(variable) => write!(f, "leaf {} for {}", self.idx, variable.label()),
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
    fn new(parent: Option<VTreeRef>, idx: VTreeIdx, node: Node) -> VTree {
        VTree {
            parent,
            idx,
            node,
            inorder_first: None,
            inorder_last: None,
        }
    }

    #[must_use]
    fn new_as_ref(parent: Option<VTreeRef>, idx: VTreeIdx, node: Node) -> VTreeRef {
        Rc::new(RefCell::new(VTree::new(parent, idx, node)))
    }

    pub(crate) fn get_index(&self) -> VTreeIdx {
        self.idx
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

    fn inorder_first_idx(&self) -> VTreeIdx {
        self.inorder_first.clone().unwrap().borrow().idx
    }

    fn inorder_last_idx(&self) -> VTreeIdx {
        self.inorder_last.clone().unwrap().borrow().idx
    }

    fn set_pointers(
        &mut self,
        inorder_first: Option<VTreeRef>,
        inorder_last: Option<VTreeRef>,
        idx: VTreeIdx,
    ) {
        self.idx = idx;
        self.inorder_first = inorder_first;
        self.inorder_last = inorder_last;
    }

    /// Collect all the variables reachable from this vtree node.
    pub(crate) fn get_variables(&self) -> BTreeSet<Variable> {
        // TODO: This can be optimized by caching.
        match self.node.clone() {
            Node::Leaf(var_label) => btreeset!(var_label),
            Node::Internal(left, right) => left
                .borrow()
                .get_variables()
                .union(&right.borrow().get_variables())
                .cloned()
                .collect::<BTreeSet<_>>(),
        }
    }

    pub(crate) fn get_parent(&self) -> Option<VTreeRef> {
        self.parent.clone()
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

#[derive(Debug)]
pub struct VTreeManager {
    pub(crate) root: Option<VTreeRef>,

    // TODO: Fix the meaningless bookkeeping and computation of
    // next_idx in `VTreeManager::add_variable`.
    next_idx: VTreeIdx,
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
            next_idx: VTreeIdx(0),
        }
    }

    /// Add variable to the variable tree. The variable is inserted to the very end of the total
    /// variable order.
    ///
    /// TODO: Allow different insertion strategies.
    pub(crate) fn add_variable(&mut self, label: &Variable) -> VTreeIdx {
        let new_leaf = VTree::new_as_ref(None, self.next_idx, Node::Leaf(label.clone()));
        new_leaf.borrow_mut().inorder_last = Some(new_leaf.clone());

        if self.root.is_none() {
            self.next_idx += VTreeIdx(1);
            self.root = Some(new_leaf);
            VTreeManager::set_inorder_indices(self.root.clone().unwrap(), VTreeIdx(0));
            return self.next_idx - VTreeIdx(1);
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
                self.next_idx += VTreeIdx(0);

                rightest.borrow_mut().parent = Some(parent.clone());
                new_leaf.borrow_mut().parent = Some(parent.clone());

                match parent.borrow().parent.as_ref() {
                    None => self.root = Some(parent.clone()),
                    Some(p_parent) => p_parent.borrow_mut().set_right_child(&parent),
                };
            }
        }

        // TODO: This can be optimized further.
        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), VTreeIdx(0));
        self.next_idx - VTreeIdx(1)
    }

    pub(crate) fn root_idx(&self) -> Option<VTreeIdx> {
        self.root.clone().map(|root| root.borrow().idx)
    }

    fn set_inorder_indices(
        node: VTreeRef,
        idx: VTreeIdx,
    ) -> (VTreeIdx, Option<VTreeRef>, Option<VTreeRef>) {
        let (new_idx, par_idx, fst, last) = if let Node::Internal(lc, rc) =
            node.borrow().node.clone()
        {
            let (new_idx, fst, _) = VTreeManager::set_inorder_indices(lc, idx);
            let (par_idx, _, last) = VTreeManager::set_inorder_indices(rc, new_idx + VTreeIdx(1));

            (new_idx, par_idx, fst, last)
        } else {
            (
                idx,
                idx + VTreeIdx(1),
                Some(node.clone()),
                Some(node.clone()),
            )
        };

        node.borrow_mut()
            .set_pointers(fst.clone(), last.clone(), new_idx);

        (par_idx, fst, last)
    }

    #[must_use]
    pub(crate) fn variables_total_order(&self) -> Vec<(Variable, VTreeIdx)> {
        fn dfs(vtree: &VTreeRef, order: &mut Vec<(Variable, VTreeIdx)>) {
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

        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), VTreeIdx(0));
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

        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), VTreeIdx(0));
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

        VTreeManager::set_inorder_indices(self.root.clone().unwrap(), VTreeIdx(0));
    }

    pub(crate) fn get_variable_vtree(&self, variable: &Variable) -> Option<VTreeRef> {
        fn find_vtree(vtree: &VTreeRef, variable: &Variable) -> Option<VTreeRef> {
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

    pub(crate) fn get_vtree(&self, index: VTreeIdx) -> Option<VTreeRef> {
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
            } else {
                panic!("vtree is malformed or vtree with index {index} does not exist");
            }
        }
    }

    pub(crate) fn least_common_ancestor(
        &self,
        fst_idx: VTreeIdx,
        snd_idx: VTreeIdx,
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
        for (variable, idx) in self.variables_total_order() {
            writer.add_node(
                idx.0 as usize,
                NodeType::CircleStr(variable.label(), idx.0 as u16),
            );
        }

        let mut nodes = vec![self.root.as_ref().unwrap().clone()];
        while let Some(vtree) = nodes.pop() {
            let vtree = vtree.borrow();
            if let Node::Internal(lc, rc) = vtree.node.clone() {
                writer.add_edge(Edge::Simple(
                    vtree.idx.0 as usize,
                    lc.borrow().idx.0 as usize,
                ));
                writer.add_edge(Edge::Simple(
                    vtree.idx.0 as usize,
                    rc.borrow().idx.0 as usize,
                ));
                nodes.push(lc.clone());
                nodes.push(rc.clone());

                writer.add_node(
                    vtree.idx.0 as usize,
                    NodeType::Circle(vtree.idx.0 as u16, None),
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
pub(crate) mod test {
    use crate::{
        literal::Variable,
        vtree::{VTreeIdx, VTreeOrder, VTreeRef},
    };

    use super::{Node, VTreeManager};

    fn orders_eq(got_order: Vec<(Variable, VTreeIdx)>, want_order: Vec<Variable>) {
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

    pub(crate) fn right_child(vtree: &VTreeRef) -> VTreeRef {
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
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));
        manager.add_variable(&Variable::new("C", 2));
        manager.add_variable(&Variable::new("D", 3));

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
        assert_eq!(root.borrow().idx.0, 3);
        assert_eq!(get_inorder_first(root.clone()).0, 0);
        assert_eq!(get_inorder_last(root.clone()).0, 6);

        let Node::Internal(lc, rc) = root.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };

        assert_eq!(lc.borrow().idx.0, 1);
        assert_eq!(get_inorder_first(lc.clone()).0, 0);
        assert_eq!(get_inorder_last(lc.clone()).0, 2);

        assert_eq!(rc.borrow().idx.0, 5);
        assert_eq!(get_inorder_first(rc.clone()).0, 4);
        assert_eq!(get_inorder_last(rc.clone()).0, 6);

        let Node::Internal(llc, lrc) = lc.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };
        assert_eq!(llc.borrow().idx.0, 0);
        assert_eq!(get_inorder_first(llc.clone()).0, 0);
        assert_eq!(get_inorder_last(llc.clone()).0, 0);

        assert_eq!(lrc.borrow().idx.0, 2);
        assert_eq!(get_inorder_first(lrc.clone()).0, 2);
        assert_eq!(get_inorder_last(lrc.clone()).0, 2);

        let Node::Internal(rlc, rrc) = rc.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };
        assert_eq!(rlc.borrow().idx.0, 4);
        assert_eq!(get_inorder_first(rlc.clone()).0, 4);
        assert_eq!(get_inorder_last(rlc.clone()).0, 4);

        assert_eq!(rrc.borrow().idx.0, 6);
        assert_eq!(get_inorder_first(rrc.clone()).0, 6);
        assert_eq!(get_inorder_last(rrc.clone()).0, 6);
    }

    #[test]
    fn structure() {
        let mut manager = VTreeManager::new();
        assert!(manager.root.is_none());

        manager.add_variable(&Variable::new("A", 1));
        assert!(manager.root.is_some());
        assert!(manager
            .root
            .clone()
            .is_some_and(|root| matches!(root.as_ref().borrow().node, Node::Leaf(..))));

        manager.add_variable(&Variable::new("B", 2));
        assert!(manager
            .root
            .clone()
            .is_some_and(|root| matches!(root.as_ref().borrow().node, Node::Internal(..))));

        manager.add_variable(&Variable::new("C", 3));

        // Test that the vtree has the following structure:
        //    *
        //   / \
        //  A   *
        //     / \
        //    B   C
        if let Node::Internal(lc, rc) = manager.root.unwrap().borrow().node.clone() {
            let a = lc.borrow().node.clone();
            assert!(matches!(a, Node::Leaf(label) if label.eq(&Variable::new("A", 1))));

            let inner = rc.borrow().node.clone();
            match inner {
                Node::Leaf(_) => panic!("Node should've been internal"),
                Node::Internal(lc, rc) => {
                    let b = lc.borrow().node.clone();
                    let c = rc.borrow().node.clone();

                    assert!(matches!(b, Node::Leaf(label) if label.eq(&Variable::new("B", 2))));
                    assert!(matches!(c, Node::Leaf(label) if label.eq(&Variable::new("C", 3))));
                }
            }
        }
    }

    #[test]
    fn variables_total_order_simple() {
        let mut manager = VTreeManager::new();
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));
        manager.add_variable(&Variable::new("C", 2));

        let want_order = vec![
            Variable::new("A", 0),
            Variable::new("B", 1),
            Variable::new("C", 2),
        ];
        orders_eq(manager.variables_total_order(), want_order);
    }

    #[test]
    fn variables_total_order_swap() {
        let mut manager = VTreeManager::new();
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));

        let root = manager.root.clone().unwrap();

        // <A, B> ~> <B, A>
        manager.swap(&root);
        orders_eq(
            manager.variables_total_order(),
            vec![Variable::new("B", 1), Variable::new("A", 0)],
        );

        // <B, A> ~> <A, B>
        manager.swap(&root);
        orders_eq(
            manager.variables_total_order(),
            vec![Variable::new("A", 0), Variable::new("B", 1)],
        );
    }

    #[test]
    fn variables_total_order() {
        let mut manager = VTreeManager::new();
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));
        manager.add_variable(&Variable::new("C", 2));
        let want_order = vec![
            Variable::new("A", 0),
            Variable::new("B", 1),
            Variable::new("C", 2),
        ];

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

                assert!(matches!(c, Node::Leaf(label) if label.eq(&Variable::new("C", 2))));

                lc.clone()
            }
        };

        match x.borrow().node.clone() {
            Node::Leaf(_) => panic!("this should've been an internal node"),
            Node::Internal(lc, rc) => {
                let a = lc.borrow().node.clone();
                let b = rc.borrow().node.clone();

                assert!(matches!(a, Node::Leaf(label) if label.eq(&Variable::new("A", 0))));
                assert!(matches!(b, Node::Leaf(label) if label.eq(&Variable::new("B", 1))));
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

                assert!(matches!(a, Node::Leaf(label) if label.eq(&Variable::new("A", 0))));

                rc.clone()
            }
        };

        match y.borrow().node.clone() {
            Node::Leaf(_) => panic!("this should've been an internal node"),
            Node::Internal(lc, rc) => {
                let b = lc.borrow().node.clone();
                let c = rc.borrow().node.clone();

                assert!(matches!(b, Node::Leaf(label) if label.eq(&Variable::new("B", 1))));
                assert!(matches!(c, Node::Leaf(label) if label.eq(&Variable::new("C", 2))));
            }
        };
    }

    #[test]
    fn least_common_ancestor() {
        let mut manager = VTreeManager::new();
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));
        manager.add_variable(&Variable::new("C", 2));
        manager.add_variable(&Variable::new("D", 3));
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
        let (lca, ord) = manager.least_common_ancestor(1_u32.into(), root_idx);
        assert_eq!(ord, VTreeOrder::LeftSubOfRight);
        assert_eq!(lca.borrow().idx, root_idx);

        // rc has index of 5
        let (lca, ord) = manager.least_common_ancestor(root_idx, 5_u32.into());
        assert_eq!(ord, VTreeOrder::RightSubOfLeft);
        assert_eq!(lca.borrow().idx, root_idx);

        // llc has index of 0, rrc has index of 6
        let (lca, ord) = manager.least_common_ancestor(0_u32.into(), 6_u32.into());
        assert_eq!(ord, VTreeOrder::Inequal);
        assert_eq!(lca.borrow().idx, root_idx);
    }

    #[test]
    fn literal_indices() {
        let var_label_index = |vtree: Option<VTreeRef>| -> VTreeIdx { vtree.unwrap().borrow().idx };

        let mut manager = VTreeManager::new();
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));
        manager.add_variable(&Variable::new("C", 2));
        manager.add_variable(&Variable::new("D", 3));
        //     1
        //   /   \
        //  0     3
        //  A   /   \
        //     2     5
        //     B   /   \
        //        4     6
        //        C     D

        assert_eq!(
            var_label_index(manager.get_variable_vtree(&Variable::new("A", 0))).0,
            0
        );
        assert_eq!(
            var_label_index(manager.get_variable_vtree(&Variable::new("B", 1))).0,
            2
        );
        assert_eq!(
            var_label_index(manager.get_variable_vtree(&Variable::new("C", 2))).0,
            4
        );
        assert_eq!(
            var_label_index(manager.get_variable_vtree(&Variable::new("D", 3))).0,
            6
        );
        assert_eq!(manager.get_variable_vtree(&Variable::new("E", 4)), None);
    }

    #[test]
    fn get_variables() {
        let mut manager = VTreeManager::new();
        manager.add_variable(&Variable::new("A", 0));
        manager.add_variable(&Variable::new("B", 1));
        manager.add_variable(&Variable::new("C", 2));
        manager.add_variable(&Variable::new("D", 3));

        let variables = manager.root.unwrap().as_ref().borrow().get_variables();
        assert_eq!(
            variables,
            btreeset!(
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
                Variable::new("D", 3)
            )
        );
    }
}
