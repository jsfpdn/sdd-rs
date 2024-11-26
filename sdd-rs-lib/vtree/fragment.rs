use tracing::instrument;

use crate::{
    manager::{SddManager, FALSE_SDD_IDX, TRUE_SDD_IDX},
    sdd::{Decision, Element, SddRef, SddType},
    vtree::{Node, VTreeRef},
};

use std::{collections::BTreeSet, rc::Rc};

#[derive(PartialEq, Debug)]
pub(crate) enum Direction {
    Forward,
    Backward,
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum Move {
    LeftRotateChild,
    RightRotateRoot,
    SwapChild,
}

const MOVES_LEFT_LINEAR: [Move; 12] = [
    Move::RightRotateRoot,
    Move::SwapChild,
    Move::LeftRotateChild,
    Move::SwapChild,
    //
    Move::RightRotateRoot,
    Move::SwapChild,
    Move::LeftRotateChild,
    Move::SwapChild,
    //
    Move::RightRotateRoot,
    Move::SwapChild,
    Move::LeftRotateChild,
    Move::SwapChild,
];

const MOVES_RIGHT_LINEAR: [Move; 12] = [
    Move::LeftRotateChild,
    Move::SwapChild,
    Move::RightRotateRoot,
    Move::SwapChild,
    //
    Move::LeftRotateChild,
    Move::SwapChild,
    Move::RightRotateRoot,
    Move::SwapChild,
    //
    Move::LeftRotateChild,
    Move::SwapChild,
    Move::RightRotateRoot,
    Move::SwapChild,
];

pub(crate) struct Fragment {
    current_root: VTreeRef,
    current_child: VTreeRef,

    state: FragmentState,
}

struct FragmentState {
    // Index points to the `forward_moves` array to the next move to be performed.
    index: usize,
    forward_moves: [Move; 12],
    backward_moves: [Move; 12],
}

enum Linearity {
    LeftLinear,
    RightLinear,
}

impl FragmentState {
    fn new(linearity: Linearity) -> Self {
        let (forward_moves, backward_moves) = match linearity {
            Linearity::LeftLinear => (MOVES_LEFT_LINEAR, MOVES_RIGHT_LINEAR),
            Linearity::RightLinear => (MOVES_RIGHT_LINEAR, MOVES_LEFT_LINEAR),
        };

        Self {
            index: 0,
            forward_moves,
            backward_moves,
        }
    }

    fn next(&mut self, direction: &Direction) -> Move {
        match direction {
            Direction::Forward => {
                assert!(self.index <= 11);
                let mv = self.forward_moves[self.index];
                self.index += 1;
                mv
            }
            Direction::Backward => {
                // Assert that we have indeed moved forward before in order to go backward.
                assert!(self.index <= 12);
                assert!(self.index != 0);
                self.index -= 1;
                self.backward_moves[self.index]
            }
        }
    }
}

/// Given the following vtree rooted at `x`:
/// ```ignore
///        x
///      /   \
///     w     c
///   /   \
///  a     b
/// ```
/// an SDD normalized for `x` must depend on some variable in sub-vtree `c`
/// and also on some variable in sub-vtree `a`, `b`, or both.
#[derive(Debug, PartialEq, Eq)]
#[allow(unused)]
pub(crate) enum LeftDependence {
    /// SDD normalized for `x` depends only on some variable in sub-vtree `a`, not `b`.
    A,
    /// SDD normalized for `x` depends only on some variable in sub-vtree `b`, not `a`.
    B,
    /// SDD normalized for `x` depends on some variables in both sub-vtrees `a` and `b`.
    AB,
}

/// Given the following vtree rooted at `w`:
/// ```ignore
///      w
///    /   \
///   a     x
///       /   \
///      b     c
/// ```
/// an SDD normalized for `w` must depend on some variable in sub-vtree `a`
/// and also on some variable in sub-vtree `b`, `c`, or both.
#[derive(Debug, PartialEq, Eq)]
#[allow(unused)]
pub(crate) enum RightDependence {
    /// SDD normalized for `x` depends only on some variable in sub-vtree `b`, not `c`.
    B,
    /// SDD normalized for `x` depends only on some variable in sub-vtree `c`, not `b`.
    C,
    /// SDD normalized for `x` depends on some variables in both sub-vtrees `b` and `c`.
    BC,
}

impl Fragment {
    #[must_use]
    pub(crate) fn new(root: VTreeRef, child: VTreeRef) -> Self {
        let linearity = match root.0.borrow().node.clone() {
            Node::Internal(lc, _) if Rc::ptr_eq(&lc.0, &child.0) => Linearity::LeftLinear,
            Node::Internal(_, rc) if Rc::ptr_eq(&rc.0, &child.0) => Linearity::RightLinear,
            _ => panic!("root and child cannot form a fragment"),
        };

        Fragment {
            current_root: root.clone(),
            current_child: child.clone(),
            state: FragmentState::new(linearity),
        }
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub(crate) fn next(&mut self, direction: &Direction, manager: &SddManager) {
        let next_move = self.state.next(direction);
        tracing::debug!(?next_move);

        match next_move {
            Move::LeftRotateChild => {
                assert!(Rc::ptr_eq(
                    &self.current_child.0,
                    &self.current_root.right_child().0
                ));
                manager.rotate_left(&self.current_child.clone());
                self.swap();
            }
            Move::RightRotateRoot => {
                assert!(Rc::ptr_eq(
                    &self.current_child.0,
                    &self.current_root.left_child().0
                ));
                manager.rotate_right(&self.current_root);
                self.swap();
            }
            Move::SwapChild => {
                assert!(Rc::ptr_eq(
                    &self.current_root.0,
                    &self.current_child.parent().unwrap().0
                ));
                manager.swap(&self.current_child);
            }
        }
    }

    pub(crate) fn rewind(&mut self, state: usize, manager: &SddManager) {
        assert!(self.state.index > state);

        while self.state.index > state {
            self.next(&Direction::Backward, manager)
        }
    }

    fn swap(&mut self) {
        let tmp = self.current_root.clone();
        self.current_root = self.current_child.clone();
        self.current_child = tmp;
    }
}

pub(crate) struct LeftRotateSplit {
    pub(crate) bc_vec: Vec<SddRef>,
    pub(crate) c_vec: Vec<SddRef>,
}

pub(crate) struct RightRotateSplit {
    pub(crate) ab_vec: Vec<SddRef>,
    pub(crate) a_vec: Vec<SddRef>,
}

/// Split SDDs in preparation for left rotation. See
/// [`sdd_vtree_rotate_left`] for more information.
///
/// This function removes split nodes from the unique table.
pub(crate) fn split_nodes_for_left_rotate(
    w: &VTreeRef,
    x: &VTreeRef,
    manager: &SddManager,
) -> LeftRotateSplit {
    // Collect all the SDDs which are normalized for `w`.
    let normalized_sdds = manager
        .get_nodes_normalized_for(w.index())
        .iter()
        .map(|(id, sdd)| (sdd.0.borrow().dependence_on_right_vtree(x, manager), *id))
        .collect::<Vec<_>>();

    let mut c_vec = Vec::new();
    let mut bc_vec = Vec::new();

    for (dependence, id) in &normalized_sdds {
        if *dependence == RightDependence::B {
            continue;
        }

        let sdd = manager.get_node(*id);
        let res = manager.remove_node(*id);
        assert!(res.is_ok(), "unique_table should've contained the SDD");

        match dependence {
            RightDependence::B => unreachable!(),
            RightDependence::C => c_vec.push(sdd),
            RightDependence::BC => bc_vec.push(sdd),
        }
    }

    LeftRotateSplit { c_vec, bc_vec }
}

pub(crate) fn split_nodes_for_right_rotate(
    x: &VTreeRef,
    w: &VTreeRef,
    manager: &SddManager,
) -> RightRotateSplit {
    let normalized_sdds = manager
        .get_nodes_normalized_for(x.index())
        .iter()
        .map(|(id, sdd)| (sdd.0.borrow().dependence_on_left_vtree(w, manager), *id))
        .collect::<Vec<_>>();

    let mut a_vec = Vec::new();
    let mut ab_vec = Vec::new();

    for (dependence, id) in &normalized_sdds {
        if *dependence == LeftDependence::B {
            continue;
        }

        let sdd = manager.get_node(*id);
        let res = manager.remove_node(*id);
        assert!(res.is_ok(), "unique_table should've contained the SDD");

        match dependence {
            LeftDependence::B => unreachable!(),
            LeftDependence::A => a_vec.push(sdd),
            LeftDependence::AB => ab_vec.push(sdd),
        }
    }

    RightRotateSplit { a_vec, ab_vec }
}

pub(crate) fn split_nodes_for_swap(v: &VTreeRef, manager: &SddManager) -> Vec<SddRef> {
    let normalized_sdds = manager.get_nodes_normalized_for(v.index());

    normalized_sdds
        .iter()
        .for_each(|(id, _)| manager.remove_node(*id).unwrap());

    normalized_sdds.iter().map(|(_, sdd)| sdd.clone()).collect()
}

/// Rotate partitions to the left.
#[must_use]
pub(crate) fn rotate_partition_left(node: &SddRef, x: &VTreeRef, manager: &SddManager) -> Decision {
    let w = x.left_child();

    // This function assumes that `x` has been already rotated and `w` is it's left child.
    let SddType::Decision(ref decision) = node.0.borrow().sdd_type else {
        panic!("node must be a decision node");
    };

    let mut elements = BTreeSet::new();
    for element in &decision.elements {
        let (a, bc) = element.get_prime_sub(manager);

        if bc.is_constant() || bc.vtree().index() > x.index() {
            elements.insert(Element {
                prime: a.id(),
                sub: bc.id(),
            });
            continue;
        }

        if bc.vtree().index() == x.index() {
            let SddType::Decision(ref bc_decision) = bc.0.borrow().sdd_type else {
                panic!("node must be a decision node");
            };

            for bc_element in bc_decision.elements.iter() {
                let (b, c) = bc_element.get_prime_sub(manager);
                // TODO: Once conjoin is able to do vtree search on it's own, turn it off in here.
                // TODO: we could improve this since we already know LCA, which is x's left child.
                let ab = manager._conjoin_rotations(&a, &b, &w);
                elements.insert(Element {
                    prime: ab.id(),
                    sub: c.id(),
                });
            }

            continue;
        }

        // last case: bc is normalized for vtree in b
        // Create element (a && bc, True).
        elements.insert(Element {
            prime: manager._conjoin_rotations(&a, &bc, &w).id(),
            sub: TRUE_SDD_IDX,
        });

        // Create element (a && !bc, False).
        elements.insert(Element {
            prime: manager._conjoin_rotations(&a, &bc.negate(manager), &w).id(),
            sub: FALSE_SDD_IDX,
        });
    }

    Decision {
        elements: elements.clone(),
    }
    .canonicalize(manager)
}

/// Rotate partitions to the right.
#[allow(unused)]
pub(crate) fn rotate_partition_right(
    node: &SddRef,
    w: &VTreeRef,
    manager: &SddManager,
) -> Decision {
    let x = w.right_child();
    let SddType::Decision(ref decision) = node.0.borrow().sdd_type else {
        panic!("node must be a decision node");
    };

    let mut elements = BTreeSet::new();
    for element in &decision.elements {
        let mut current_elements = BTreeSet::new();

        let (ab, c) = element.get_prime_sub(manager);
        assert!(!ab.is_constant());

        if ab.vtree().index() >= x.inorder_first() && ab.vtree().index() <= x.inorder_last() {
            current_elements.insert(Element {
                prime: TRUE_SDD_IDX,
                sub: manager._conjoin_rotations(&ab, &c, &x).id(),
            });
        } else if ab.vtree().index() == w.index() {
            let SddType::Decision(ref ab_decision) = ab.0.borrow().sdd_type else {
                panic!("node must be a decision node");
            };

            for ab_element in &ab_decision.elements {
                let (a, b) = ab_element.get_prime_sub(manager);
                let bc = manager._conjoin_rotations(&b, &c, &x);
                current_elements.insert(Element {
                    prime: a.id(),
                    sub: bc.id(),
                });
            }
        } else {
            current_elements.insert(Element {
                prime: ab.id(),
                sub: c.id(),
            });

            current_elements.insert(Element {
                prime: ab.negate(manager).id(),
                sub: FALSE_SDD_IDX,
            });
        }

        elements = cartesian_product(elements.clone(), current_elements.clone(), manager);
    }

    Decision { elements }.canonicalize(manager)
}

pub(crate) fn swap_partition(node: &SddRef, manager: &SddManager) -> Decision {
    let SddType::Decision(ref decision) = node.0.borrow().sdd_type else {
        panic!("node must be a decision node");
    };

    let mut elements = BTreeSet::new();
    for element in &decision.elements {
        let mut current_elements = BTreeSet::new();

        let (a, b) = element.get_prime_sub(manager);
        let neg_b = manager.negate(&b);
        if !b.is_false() {
            current_elements.insert(Element {
                prime: b.id(),
                sub: a.id(),
            });
        }

        if !neg_b.is_false() {
            current_elements.insert(Element {
                prime: neg_b.id(),
                sub: FALSE_SDD_IDX,
            });
        }

        elements = cartesian_product(current_elements, elements, manager);
    }

    Decision { elements }.canonicalize(manager)
}

fn cartesian_product(
    fst: BTreeSet<Element>,
    snd: BTreeSet<Element>,
    manager: &SddManager,
) -> BTreeSet<Element> {
    if fst.is_empty() {
        return snd.clone();
    }

    if snd.is_empty() {
        return fst.clone();
    }

    let mut out = BTreeSet::new();

    for fst_element in &fst {
        for snd_element in &snd {
            let (fst_prime, fst_sub) = fst_element.get_prime_sub(manager);
            let (snd_prime, snd_sub) = snd_element.get_prime_sub(manager);

            let res_prime = manager.conjoin(&fst_prime, &snd_prime);
            if !res_prime.is_false() {
                let res_sub = manager.disjoin(&fst_sub, &snd_sub);

                out.insert(Element {
                    prime: res_prime.id(),
                    sub: res_sub.id(),
                });
            }
        }
    }

    out
}

#[cfg(test)]
mod test {
    use crate::{
        literal::Polarity,
        manager::{
            options::{vars, SddOptions, VTreeStrategy},
            SddManager,
        },
        vtree::fragment::{FragmentState, Linearity, Move},
    };

    use super::{Direction, Fragment};

    use pretty_assertions::assert_eq;

    #[test]
    fn fragment_forward() {
        // We should be able to create minimal right-linear fragment and visit all the
        // possible states while going forward.
        let options = SddOptions::builder()
            .vtree_strategy(VTreeStrategy::RightLinear)
            .variables(vars(vec!["a", "b", "c"]))
            .build();
        let manager = SddManager::new(options);

        let lit_a = manager.literal("a", Polarity::Positive);
        let lit_b = manager.literal("b", Polarity::Positive);
        let lit_c = manager.literal("c", Polarity::Positive);

        //           1
        //         /   \
        //        A     3
        //            /   \
        //           B     C

        let a_and_b = manager.conjoin(&lit_a, &lit_b);
        let a_and_b_or_c = manager.disjoin(&a_and_b, &lit_c);
        let models = manager.model_enumeration(&a_and_b_or_c);

        let root = manager.root().unwrap();
        let rc = root.right_child();
        let mut fragment = Fragment::new(root.clone(), rc.clone());

        for i in 0..=11 {
            let next_move = fragment.state.forward_moves[fragment.state.index];
            fragment.next(&Direction::Forward, &manager);

            assert_eq!(
                models,
                manager.model_enumeration(&a_and_b_or_c),
                "{i}-th state failed after doing {next_move:?}",
            );
        }

        // Try to roll back to the 5th state (e.g. RR, SC, LR, SC, RR)
        fragment.rewind(5, &manager);
        assert_eq!(fragment.state.index, 5);
    }

    #[test]
    fn move_between_states() {
        use Direction::*;
        use Move::*;

        // Order of operations when going forward must be RR, SC, LR, SC, RR.
        // When rewinding and rolling it back, the operations should be inverse
        // (inverse(RR) = LL, inverse(LL) = RR, inverse(SC) = SC) and in the
        // inverse order.

        let mut state = FragmentState::new(Linearity::LeftLinear);
        assert_eq!(state.next(&Forward), RightRotateRoot);
        assert_eq!(state.index, 1);

        assert_eq!(state.next(&Forward), SwapChild);
        assert_eq!(state.index, 2);

        assert_eq!(state.next(&Forward), LeftRotateChild);
        assert_eq!(state.index, 3);

        assert_eq!(state.next(&Forward), SwapChild);
        assert_eq!(state.index, 4);

        assert_eq!(state.next(&Forward), RightRotateRoot);
        assert_eq!(state.index, 5);

        assert_eq!(state.next(&Backward), LeftRotateChild);
        assert_eq!(state.index, 4);

        assert_eq!(state.next(&Backward), SwapChild);
        assert_eq!(state.index, 3);

        assert_eq!(state.next(&Backward), RightRotateRoot);
        assert_eq!(state.index, 2);

        assert_eq!(state.next(&Backward), SwapChild);
        assert_eq!(state.index, 1);

        assert_eq!(state.next(&Backward), LeftRotateChild);
        assert_eq!(state.index, 0);
    }
}
