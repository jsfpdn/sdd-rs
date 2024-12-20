#![allow(clippy::non_canonical_partial_ord_impl, clippy::similar_names)]

use crate::{
    dot_writer::{Dot, DotWriter, EdgeType, NodeType},
    literal::Variable,
    manager::options::VTreeStrategy,
};
use anyhow::{bail, Result};
use derive_more::derive::{Add, AddAssign, From, Sub};
use std::{
    cell::RefCell,
    collections::{BTreeSet, VecDeque},
    fmt::{Debug, Display},
    rc::Rc,
};

use super::{Fragment, Linearity};

/// Node of a full binary tree.
#[derive(Clone, PartialEq)]
pub(crate) enum Node {
    Leaf(Variable),
    Internal(VTreeRef, VTreeRef),
}

/// Index of a vtree node given by the inorder traversal starting from the root.
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug, Copy, Add, AddAssign, Sub, From)]
pub struct VTreeIdx(pub u32);

impl Display for VTreeIdx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// Vtree is a node of a full binary tree.
#[derive(PartialEq, Clone)]
pub(crate) struct VTree {
    parent: Option<VTreeRef>,
    // Index according to the inorder traversal of the VTree. Can change when manipulating the tree in any way,
    // e.g. adding/removing variables and swapping or rotating nodes.
    idx: VTreeIdx,

    // Pointer to first vtree node in the subtree given by the current node
    // according to the inorder.
    inorder_first: Option<VTreeRef>,
    // Pointer to first vtree node in the subtree given by the current node
    // according to the inorder.
    inorder_last: Option<VTreeRef>,

    pub(crate) node: Node,
}

impl Debug for VTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.node.clone() {
            Node::Leaf(variable) => write!(f, "leaf {} for {}", self.idx, variable.label()),
            Node::Internal(lc, rc) => write!(
                f,
                "internal {} ({}, {})",
                self.idx,
                lc.0.borrow().idx,
                rc.0.borrow().idx
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

    /// Sets the left child of this [`VTree`].
    ///
    /// # Panics
    ///
    /// Panics if the vtree does not represent an internal node.
    fn set_left_child(&mut self, left_child: &VTreeRef) {
        match self.node {
            Node::Leaf(_) => panic!("should not happen!"),
            Node::Internal(ref mut lc, _) => *lc = left_child.clone(),
        }
    }

    /// Sets the right child of this [`VTree`].
    ///
    /// # Panics
    ///
    /// Panics if the vtree does not represent an internal node.
    fn set_right_child(&mut self, right_child: &VTreeRef) {
        match self.node {
            Node::Leaf(_) => panic!("should not happen!"),
            Node::Internal(_, ref mut rc) => *rc = right_child.clone(),
        }
    }

    fn inorder_first_idx(&self) -> VTreeIdx {
        self.inorder_first.clone().unwrap().index()
    }

    fn inorder_last_idx(&self) -> VTreeIdx {
        self.inorder_last.clone().unwrap().index()
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
                .0
                .borrow()
                .get_variables()
                .union(&right.0.borrow().get_variables())
                .cloned()
                .collect::<BTreeSet<_>>(),
        }
    }

    pub(crate) fn get_parent(&self) -> Option<VTreeRef> {
        self.parent.clone()
    }
}

/// `VTreeOrder` describes the relation between two vtrees.
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

/// Vtree is a node of a full binary tree for which an [`crate::sdd::SddRef`] is normalized.
#[derive(Debug, Clone)]
pub struct VTreeRef(pub(crate) Rc<RefCell<VTree>>);

impl PartialOrd for VTreeRef {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.index().partial_cmp(&other.index())
    }
}

impl Ord for VTreeRef {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.index().cmp(&other.index())
    }
}

impl PartialEq for VTreeRef {
    fn eq(&self, other: &Self) -> bool {
        self.index() == other.index()
    }
}

impl Eq for VTreeRef {}

impl VTreeRef {
    pub(crate) fn new(parent: Option<VTreeRef>, idx: VTreeIdx, node: Node) -> Self {
        VTreeRef(Rc::new(RefCell::new(VTree::new(parent, idx, node))))
    }

    /// Returns true if the vtree is a leaf node.
    #[must_use]
    pub fn is_leaf(&self) -> bool {
        matches!(self.0.borrow().node, Node::Leaf(..))
    }

    /// Returns true if the vtree is an internal node.
    #[must_use]
    pub fn is_internal(&self) -> bool {
        matches!(self.0.borrow().node, Node::Internal(..))
    }

    /// Returns its left child if the vtree is an internal node.
    /// Otherwise returns [`Option::None`].
    #[must_use]
    pub fn left_child(&self) -> Option<VTreeRef> {
        match self.0.borrow().node {
            Node::Leaf(_) => None,
            Node::Internal(ref lc, _) => Some(lc.clone()),
        }
    }

    /// Returns its right child if the vtree is an internal node.
    /// Otherwise returns [`Option::None`].
    #[must_use]
    pub fn right_child(&self) -> Option<VTreeRef> {
        match self.0.borrow().node {
            Node::Leaf(_) => None,
            Node::Internal(_, ref rc) => Some(rc.clone()),
        }
    }

    /// Returns its parent if the vtree has one.
    #[must_use]
    pub fn parent(&self) -> Option<VTreeRef> {
        self.0.borrow().parent.clone()
    }

    /// Returns index of the vtree given by inorder traversal starting from the root.
    #[must_use]
    pub fn index(&self) -> VTreeIdx {
        self.0.borrow().idx
    }

    /// Create {left,right}-linear fragment with this vtree as the fragment root.
    /// Returns none if the fragment cannot be created (when either the vtree or
    /// its child depending on [`Linearity`] are not internal nodes)
    #[must_use]
    pub fn fragment(&self, linearity: Linearity) -> Option<Fragment> {
        match self.0.borrow().node {
            Node::Leaf(..) => None,
            Node::Internal(ref lc, ref rc) => {
                let child = match linearity {
                    Linearity::LeftLinear => lc.clone(),
                    Linearity::RightLinear => rc.clone(),
                };

                if child.is_internal() {
                    Some(Fragment::new(self, &child))
                } else {
                    None
                }
            }
        }
    }

    pub(crate) fn inorder_first(&self) -> VTreeIdx {
        self.0.borrow().inorder_first.as_ref().unwrap().index()
    }

    pub(crate) fn inorder_last(&self) -> VTreeIdx {
        self.0.borrow().inorder_last.as_ref().unwrap().index()
    }

    fn set_parent(&self, parent: Option<&VTreeRef>) {
        self.0.borrow_mut().parent = parent.cloned();
    }

    fn set_left_child(&self, left_child: &VTreeRef) {
        self.0.borrow_mut().set_left_child(left_child);
    }

    fn set_right_child(&self, right_child: &VTreeRef) {
        self.0.borrow_mut().set_right_child(right_child);
    }
}

/// [`VTreeManager`] is responsible for storing, indexing, retrieving
/// and manipulating vtrees.
#[derive(Debug)]
pub(crate) struct VTreeManager {
    pub(crate) root: VTreeRef,
}

impl VTreeManager {
    /// Create a new [`VTreeManager`] and construct an initial vtree covering [`variables`].
    /// The order of [`variables`] is respected by the initial vtree. [`VTreeStrategy`]
    /// dictates the dissection of this total order.
    #[must_use]
    pub(crate) fn new(strategy: VTreeStrategy, variables: &[Variable]) -> VTreeManager {
        let root = match strategy {
            VTreeStrategy::Balanced => VTreeManager::balanced(variables),
            VTreeStrategy::RightLinear => VTreeManager::right_linear(variables),
            VTreeStrategy::LeftLinear => VTreeManager::left_linear(variables),
        };
        VTreeManager::set_inorder_indices(&root, VTreeIdx(0));
        VTreeManager { root }
    }

    pub(crate) fn root(&self) -> VTreeRef {
        self.root.clone()
    }

    /// Construct a balanced vtree.
    fn balanced(variables: &[Variable]) -> VTreeRef {
        assert!(!variables.is_empty());

        let mut nodes: Vec<_> = variables
            .iter()
            // VTreeIdx is initially set to 0 for every node in the vtree,
            // we will fix it with additional pass once the tree is completely constructed.
            .map(|variable| VTreeRef::new(None, VTreeIdx(0), Node::Leaf(variable.clone())))
            .collect();

        while nodes.len() > 1 {
            let mut parents = Vec::with_capacity(nodes.len() / 2);
            for i in (0..nodes.len()).step_by(2) {
                if i + 1 == nodes.len() {
                    continue;
                }
                let lc = nodes.get(i).unwrap();
                let rc = nodes.get(i + 1).unwrap();

                let parent =
                    VTreeRef::new(None, VTreeIdx(0), Node::Internal(lc.clone(), rc.clone()));

                lc.set_parent(Some(&parent));
                rc.set_parent(Some(&parent));

                parents.push(parent);
            }

            if nodes.len() % 2 == 1 {
                parents.push(nodes.last().unwrap().clone());
            }

            nodes = parents;
        }

        nodes.first().unwrap().clone()
    }

    /// Construct a right-linear vtree.
    fn right_linear(variables: &[Variable]) -> VTreeRef {
        fn combine_rightmost(nodes: &mut VecDeque<VTreeRef>) {
            // Pop the last two nodes, create their parent and place
            // the parent back to the vector.
            assert!(nodes.len() >= 2);

            let rc = nodes.pop_back().unwrap();
            let lc = nodes.pop_back().unwrap();

            let parent = VTreeRef::new(None, VTreeIdx(0), Node::Internal(lc.clone(), rc.clone()));
            lc.set_parent(Some(&parent));
            rc.set_parent(Some(&parent));

            nodes.push_back(parent);
        }

        assert!(!variables.is_empty());
        VTreeManager::linear(variables, combine_rightmost)
    }

    /// Construct a left-linear vtree.
    fn left_linear(variables: &[Variable]) -> VTreeRef {
        fn combine_leftmost(nodes: &mut VecDeque<VTreeRef>) {
            // Pop the last two nodes, create their parent and place
            // the parent back to the vector.
            assert!(nodes.len() >= 2);

            let lc = nodes.pop_front().unwrap();
            let rc = nodes.pop_front().unwrap();

            let parent = VTreeRef::new(None, VTreeIdx(0), Node::Internal(lc.clone(), rc.clone()));
            lc.set_parent(Some(&parent));
            rc.set_parent(Some(&parent));

            nodes.push_front(parent);
        }

        assert!(!variables.is_empty());
        VTreeManager::linear(variables, combine_leftmost)
    }

    /// Construct a {left,right}-linear vtree depending on the [`combine_in_place`] function povided.
    fn linear(variables: &[Variable], combine_in_place: fn(&mut VecDeque<VTreeRef>)) -> VTreeRef {
        let mut nodes: VecDeque<_> = variables
                   .iter()
                   // VTreeIdx is initially set to 0 for every node in the vtree,
                   // we will fix it with additional pass once the tree is completely constructed.
                   .map(|variable| VTreeRef::new(None, VTreeIdx(0), Node::Leaf(variable.clone())))
                   .collect();

        if nodes.len() == 1 {
            return nodes.pop_front().unwrap().clone();
        }

        while nodes.len() >= 2 {
            combine_in_place(&mut nodes);
        }

        nodes.pop_front().unwrap().clone()
    }

    fn set_inorder_indices(
        node: &VTreeRef,
        idx: VTreeIdx,
    ) -> (VTreeIdx, Option<VTreeRef>, Option<VTreeRef>) {
        let (new_idx, par_idx, fst, last) = if let Node::Internal(lc, rc) =
            node.0.borrow().node.clone()
        {
            let (new_idx, fst, _) = VTreeManager::set_inorder_indices(&lc, idx);
            let (par_idx, _, last) = VTreeManager::set_inorder_indices(&rc, new_idx + VTreeIdx(1));

            (new_idx, par_idx, fst, last)
        } else {
            (
                idx,
                idx + VTreeIdx(1),
                Some(node.clone()),
                Some(node.clone()),
            )
        };

        node.0
            .borrow_mut()
            .set_pointers(fst.clone(), last.clone(), new_idx);

        (par_idx, fst, last)
    }

    /// Get total variable order given by the vtree.
    #[must_use]
    pub(crate) fn variables_total_order(&self) -> Vec<(Variable, VTreeIdx)> {
        fn dfs(vtree: &VTreeRef, order: &mut Vec<(Variable, VTreeIdx)>) {
            let idx = vtree.index();
            match vtree.0.borrow().node {
                Node::Leaf(ref label) => order.push((label.clone(), idx)),
                Node::Internal(ref lc, ref rc) => {
                    dfs(lc, order);
                    dfs(rc, order);
                }
            }
        }

        let mut order = Vec::new();
        dfs(&self.root, &mut order);

        order
    }

    /// Rotates the vtree to the left. Given the following tree,
    ///
    /// ```text
    ///       w
    ///      / \
    ///     a   x
    ///        / \
    ///       b   c
    /// ```
    ///
    /// `rotate_left(x)` will mutate the tree as follows:
    ///
    /// ```text
    ///       x
    ///      / \
    ///     w   c
    ///    / \
    ///   a   b
    /// ```
    ///
    /// User must make sure that the vtree `x` is 'rotatable',
    /// i.e. `x` is an internal node and has a parent.
    ///
    /// # Errors
    ///
    /// Returns an error if called on a vtree that cannot be rotated.
    pub(crate) fn rotate_left(&mut self, x: &VTreeRef) -> Result<()> {
        let Some(w) = x.parent() else {
            bail!("{} must not be a root", x.index())
        };

        let Some(b) = x.left_child() else {
            bail!("{} must be an internal node", x.index())
        };
        let parent = w.parent();

        w.set_right_child(&b);
        w.set_parent(Some(x));

        b.set_parent(Some(&w));

        x.set_left_child(&w);
        x.set_parent(parent.as_ref());

        if let Some(parent) = parent {
            let insides = { parent.0.borrow().node.clone() };

            match insides {
                Node::Internal(lc, _) if lc == w => parent.set_left_child(x),
                Node::Internal(_, rc) if rc == w => parent.set_right_child(x),
                _ => unreachable!(),
            }
        } else {
            self.root = x.clone();
        }

        VTreeManager::set_inorder_indices(&self.root, VTreeIdx(0));
        Ok(())
    }

    /// Rotates the vtree to the right. Given the following tree,
    ///
    /// ```text
    ///       x
    ///      / \
    ///     w   c
    ///    / \
    ///   a   b
    /// ```
    ///
    /// `rotate_right(x)` will mutate the tree as follows:
    ///
    /// ```text
    ///      w
    ///     / \
    ///    a   x
    ///       / \
    ///      b   c
    /// ```
    ///
    /// User must make sure that the vtree `x` is 'rotatable',
    /// i.e. `x` is an internal node and its left child `w`
    /// is also an internal node.
    ///
    /// # Errors
    ///
    /// Returns an error if called on a vtree that cannot be rotated.
    pub(crate) fn rotate_right(&mut self, x: &VTreeRef) -> Result<()> {
        let Some(w) = x.left_child() else {
            bail!("{} must be an internal node", x.index())
        };
        let Some(b) = w.right_child() else {
            bail!("left child of {} must be an internal node", w.index())
        };
        let parent = x.parent();

        x.set_parent(Some(&w));
        x.set_left_child(&b);
        b.set_parent(Some(x));

        w.set_right_child(x);
        w.set_parent(parent.as_ref());

        if let Some(parent) = parent {
            let insides = { parent.0.borrow().node.clone() };
            match insides {
                Node::Internal(lc, _) if lc == *x => parent.set_left_child(&w),
                Node::Internal(_, rc) if rc == *x => parent.set_right_child(&w),
                _ => unreachable!(),
            }
        } else {
            self.root = w.clone();
        }

        VTreeManager::set_inorder_indices(&self.root, VTreeIdx(0));
        Ok(())
    }

    /// Swaps children of internal node.
    ///
    /// # Errors
    ///
    /// Returns an error if called on a vtree representing a leaf node.
    pub(crate) fn swap(&mut self, vtree: &VTreeRef) -> Result<()> {
        {
            let mut borrowed = vtree.0.borrow_mut();
            match &borrowed.node {
                Node::Leaf(_) => bail!("cannot swap children of a leaf node"),
                Node::Internal(lc, rc) => {
                    borrowed.node = Node::Internal(rc.clone(), lc.clone());
                }
            }
        }

        VTreeManager::set_inorder_indices(&self.root, VTreeIdx(0));
        Ok(())
    }

    /// Get a leaf vtree given the variable it covers.
    ///
    /// # Panics
    ///
    /// Function panics if no such vtree exists which suggests a bug
    /// in [`SddManager`] initialization.
    pub(crate) fn get_variable_vtree(&self, variable: &Variable) -> VTreeRef {
        fn find_vtree(vtree: &VTreeRef, variable: &Variable) -> Option<VTreeRef> {
            match vtree.0.borrow().node.clone() {
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

        find_vtree(&self.root, variable).unwrap()
    }

    /// Get a vtree given its index. Returns [`Options::None`] if no such
    /// vtree exists. This happens only when there's a bug in [`SddManager`]
    /// initialization but we return it instead of panicking for better error reporting.
    pub(crate) fn get_vtree(&self, index: VTreeIdx) -> Option<VTreeRef> {
        let mut current = self.root.clone();
        loop {
            let current_index = current.index();
            if current_index == index {
                return Some(current);
            }

            if let Node::Internal(ref lc, ref rc) = current.clone().0.borrow().node {
                if index < current_index {
                    current = lc.clone();
                } else {
                    current = rc.clone();
                }
            } else {
                return None;
            }
        }
    }

    /// Compute the closest common ancestor of two vtrees.
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
            .unwrap_or_else(|| panic!("vtree with index {fst_idx} does not exist"));
        let snd = self
            .get_vtree(snd_idx)
            .unwrap_or_else(|| panic!("vtree with index {snd_idx} does not exist"));

        if fst_idx == snd_idx {
            return (fst.clone(), VTreeOrder::Equal);
        }

        if fst_idx >= snd.0.borrow().inorder_first_idx() {
            return (snd.clone(), VTreeOrder::LeftSubOfRight);
        }

        if snd_idx <= fst.0.borrow().inorder_last_idx() {
            return (fst.clone(), VTreeOrder::RightSubOfLeft);
        }

        let mut lca = fst.0.borrow().parent.clone().unwrap();
        while snd_idx > lca.0.borrow().inorder_last_idx() {
            lca = {
                let parent = lca.0.borrow().parent.clone().unwrap();
                parent
            }
        }

        (lca, VTreeOrder::Inequal)
    }
}

impl Dot for VTreeManager {
    fn draw(&self, writer: &mut DotWriter) {
        // Get the total order first to neatly order the leaf nodes in the graph.
        for (variable, idx) in self.variables_total_order() {
            writer.add_node(idx.0 as usize, NodeType::Circle(variable.label(), None));
        }

        let mut nodes = vec![self.root.clone()];
        while let Some(vtree) = nodes.pop() {
            let vtree = vtree.0.borrow();
            if let Node::Internal(lc, rc) = vtree.node.clone() {
                writer.add_edge(EdgeType::Simple(
                    vtree.idx.0 as usize,
                    lc.index().0 as usize,
                ));
                writer.add_edge(EdgeType::Simple(
                    vtree.idx.0 as usize,
                    rc.index().0 as usize,
                ));
                nodes.push(lc.clone());
                nodes.push(rc.clone());

                writer.add_node(
                    vtree.idx.0 as usize,
                    NodeType::Circle(vtree.idx.0.to_string(), None),
                );
            };
        }
    }
}

#[cfg(test)]
pub(crate) mod test {
    use crate::{
        literal::Variable,
        manager::options::VTreeStrategy,
        vtree::{VTreeIdx, VTreeOrder, VTreeRef},
    };

    use super::{Node, VTreeManager};

    fn orders_eq(got_order: &[(Variable, VTreeIdx)], want_order: &[Variable]) {
        for ((got, _), want) in got_order.to_vec().iter().zip(&want_order.to_vec()) {
            assert_eq!(got, want);
        }
        assert_eq!(got_order.len(), want_order.len());
    }

    #[test]
    fn inorder_traversal() {
        // Helper functions to retrieve indices of first and last nodes according
        // to the inorder in a given sub-vtree.
        let get_inorder_first =
            |vref: VTreeRef| vref.0.borrow().inorder_first.clone().unwrap().index();
        let get_inorder_last =
            |vref: VTreeRef| vref.0.borrow().inorder_last.clone().unwrap().index();

        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D
        let manager = VTreeManager::new(
            VTreeStrategy::Balanced,
            &[
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
                Variable::new("D", 3),
            ],
        );

        let root = manager.root.clone();
        assert_eq!(root.index().0, 3);
        assert_eq!(get_inorder_first(root.clone()).0, 0);
        assert_eq!(get_inorder_last(root.clone()).0, 6);

        let Node::Internal(lc, rc) = root.0.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };

        assert_eq!(lc.index().0, 1);
        assert_eq!(get_inorder_first(lc.clone()).0, 0);
        assert_eq!(get_inorder_last(lc.clone()).0, 2);

        assert_eq!(rc.index().0, 5);
        assert_eq!(get_inorder_first(rc.clone()).0, 4);
        assert_eq!(get_inorder_last(rc.clone()).0, 6);

        let Node::Internal(llc, lrc) = lc.0.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };
        assert_eq!(llc.index().0, 0);
        assert_eq!(get_inorder_first(llc.clone()).0, 0);
        assert_eq!(get_inorder_last(llc.clone()).0, 0);

        assert_eq!(lrc.index().0, 2);
        assert_eq!(get_inorder_first(lrc.clone()).0, 2);
        assert_eq!(get_inorder_last(lrc.clone()).0, 2);

        let Node::Internal(rlc, rrc) = rc.0.borrow().node.clone() else {
            panic!("root must be an internal node, not a leaf")
        };
        assert_eq!(rlc.index().0, 4);
        assert_eq!(get_inorder_first(rlc.clone()).0, 4);
        assert_eq!(get_inorder_last(rlc.clone()).0, 4);

        assert_eq!(rrc.index().0, 6);
        assert_eq!(get_inorder_first(rrc.clone()).0, 6);
        assert_eq!(get_inorder_last(rrc.clone()).0, 6);
    }

    #[test]
    fn structure() {
        let manager = VTreeManager::new(
            VTreeStrategy::RightLinear,
            &[
                Variable::new("A", 1),
                Variable::new("B", 2),
                Variable::new("C", 3),
            ],
        );

        // Test that the vtree has the following structure:
        //    *
        //   / \
        //  A   *
        //     / \
        //    B  C
        if let Node::Internal(lc, rc) = manager.root.0.clone().borrow().node.clone() {
            let a = lc.0.borrow().node.clone();
            assert!(matches!(a, Node::Leaf(label) if label.eq(&Variable::new("A", 1))));

            let inner = rc.0.borrow().node.clone();
            match inner {
                Node::Leaf(_) => panic!("Node should've been internal"),
                Node::Internal(lc, rc) => {
                    let b = lc.0.borrow().node.clone();
                    let c = rc.0.borrow().node.clone();

                    assert!(matches!(b, Node::Leaf(label) if label.eq(&Variable::new("B", 2))));
                    assert!(matches!(c, Node::Leaf(label) if label.eq(&Variable::new("C", 3))));
                }
            }
        }
    }

    #[test]
    fn variables_total_order_simple() {
        let manager = VTreeManager::new(
            VTreeStrategy::RightLinear,
            &[
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
            ],
        );

        let want_order = [
            Variable::new("A", 0),
            Variable::new("B", 1),
            Variable::new("C", 2),
        ];
        orders_eq(&manager.variables_total_order(), &want_order);
    }

    #[test]
    fn variables_total_order_swap() {
        let mut manager = VTreeManager::new(
            VTreeStrategy::Balanced,
            &[Variable::new("A", 0), Variable::new("B", 1)],
        );
        let root = manager.root.clone();

        // <A, B> ~> <B, A>
        manager.swap(&root).unwrap();
        orders_eq(
            &manager.variables_total_order(),
            &[Variable::new("B", 1), Variable::new("A", 0)],
        );

        // <B, A> ~> <A, B>
        manager.swap(&root).unwrap();
        orders_eq(
            &manager.variables_total_order(),
            &[Variable::new("A", 0), Variable::new("B", 1)],
        );
    }

    #[test]
    fn variables_total_order() {
        let mut manager = VTreeManager::new(
            VTreeStrategy::RightLinear,
            &[
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
            ],
        );
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

        let x = manager.root.clone().0.borrow().node.clone();

        let y = match x {
            Node::Leaf(_) => panic!("cannot happen"),
            Node::Internal(_, rc) => rc,
        };

        manager.rotate_left(&y).unwrap();

        // The total order must not change when rotating.
        orders_eq(&manager.variables_total_order(), &want_order);

        // The tree must look like this:
        //     y
        //    / \
        //   x   C
        //  / \
        // A   B

        let y = manager.root.clone();
        let x = match y.0.borrow().node {
            Node::Leaf(_) => panic!("root cannot be currently a leaf"),
            Node::Internal(ref lc, ref rc) => {
                let c = rc.0.borrow().node.clone();

                assert!(matches!(c, Node::Leaf(label) if label.eq(&Variable::new("C", 2))));

                lc.clone()
            }
        };

        match x.0.borrow().node.clone() {
            Node::Leaf(_) => panic!("this should've been an internal node"),
            Node::Internal(lc, rc) => {
                let a = lc.0.borrow().node.clone();
                let b = rc.0.borrow().node.clone();

                assert!(matches!(a, Node::Leaf(label) if label.eq(&Variable::new("A", 0))));
                assert!(matches!(b, Node::Leaf(label) if label.eq(&Variable::new("B", 1))));
            }
        };

        manager.rotate_right(&y).unwrap();

        // The total order must not change when rotating.
        orders_eq(&manager.variables_total_order(), &want_order);

        // The tree should like exactly like in the beginning:
        //    x
        //   / \
        //  A   y
        //     / \
        //    B   C

        let x = manager.root.0.borrow().node.clone();
        let y = match x {
            Node::Leaf(_) => panic!("root cannot be currently a leaf"),
            Node::Internal(lc, rc) => {
                let a = lc.0.borrow().node.clone();

                assert!(matches!(a, Node::Leaf(label) if label.eq(&Variable::new("A", 0))));

                rc.clone()
            }
        };

        match y.0.borrow().node.clone() {
            Node::Leaf(_) => panic!("this should've been an internal node"),
            Node::Internal(lc, rc) => {
                let b = lc.0.borrow().node.clone();
                let c = rc.0.borrow().node.clone();

                assert!(matches!(b, Node::Leaf(label) if label.eq(&Variable::new("B", 1))));
                assert!(matches!(c, Node::Leaf(label) if label.eq(&Variable::new("C", 2))));
            }
        };
    }

    #[test]
    fn least_common_ancestor() {
        let manager = VTreeManager::new(
            VTreeStrategy::Balanced,
            &[
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
                Variable::new("D", 3),
            ],
        );
        //           3
        //         /   \
        //        1     5
        //      / |     | \
        //     0  2     4  6
        //     A  B     C  D

        let root = manager.root.clone();
        let root_idx = root.index();

        // root has index of 3
        let (lca, ord) = manager.least_common_ancestor(root_idx, root_idx);
        assert_eq!(ord, VTreeOrder::Equal);
        assert_eq!(lca.index(), root_idx);

        // lc has index of 1
        let (lca, ord) = manager.least_common_ancestor(1_u32.into(), root_idx);
        assert_eq!(ord, VTreeOrder::LeftSubOfRight);
        assert_eq!(lca.index(), root_idx);

        // rc has index of 5
        let (lca, ord) = manager.least_common_ancestor(root_idx, 5_u32.into());
        assert_eq!(ord, VTreeOrder::RightSubOfLeft);
        assert_eq!(lca.index(), root_idx);

        // llc has index of 0, rrc has index of 6
        let (lca, ord) = manager.least_common_ancestor(0_u32.into(), 6_u32.into());
        assert_eq!(ord, VTreeOrder::Inequal);
        assert_eq!(lca.index(), root_idx);
    }

    #[test]
    fn literal_indices() {
        let var_label_index = |vtree: VTreeRef| -> VTreeIdx { vtree.index() };
        let manager = VTreeManager::new(
            VTreeStrategy::RightLinear,
            &[
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
                Variable::new("D", 3),
            ],
        );
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
    }

    #[test]
    fn get_variables() {
        let manager = VTreeManager::new(
            VTreeStrategy::LeftLinear,
            &[
                Variable::new("A", 0),
                Variable::new("B", 1),
                Variable::new("C", 2),
                Variable::new("D", 3),
            ],
        );

        let variables = manager.root.0.borrow().get_variables();
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
