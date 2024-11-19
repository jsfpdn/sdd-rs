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

#[derive(PartialEq, Eq, Debug)]
enum Mode {
    Initial,
    Next,
    Goto,
}

#[derive(Copy, Clone, Debug)]
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

#[derive(Debug)]
enum Linearity {
    Left,
    Right,
}

impl Mode {
    fn can_transition(&self, next_state: Mode) -> bool {
        match self {
            Mode::Initial => true,
            Mode::Next => next_state != Mode::Goto,
            Mode::Goto => next_state != Mode::Next,
        }
    }
}

// TODO: Fragment shadows

pub(crate) struct Fragment {
    current_root: VTreeRef,
    current_child: VTreeRef,

    state: usize,
    mode: Mode,
    linearity: Linearity,

    moves: [Move; 12],
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
    // TODO: implement iterator over fragment states.
    // TODO: think about limits & rolling back states.
    #[must_use]
    pub(crate) fn new(root: VTreeRef, child: VTreeRef) -> Self {
        let (linearity, moves) = match root.0.borrow().node.clone() {
            Node::Internal(lc, _) if Rc::ptr_eq(&lc.0, &child.0) => {
                (Linearity::Left, MOVES_LEFT_LINEAR)
            }
            Node::Internal(_, rc) if Rc::ptr_eq(&rc.0, &child.0) => {
                (Linearity::Right, MOVES_RIGHT_LINEAR)
            }
            _ => panic!("root and child cannot form a fragment"),
        };

        Fragment {
            current_root: root.clone(),
            current_child: child.clone(),
            linearity,
            state: 0,
            mode: Mode::Initial,
            moves,
        }
    }

    #[instrument(skip_all, ret, level = tracing::Level::DEBUG)]
    pub(crate) fn next(&mut self, direction: &Direction, manager: &SddManager) {
        assert!(self.state <= 11);
        assert!(
            self.mode.can_transition(Mode::Next),
            "cannot transition from {:?} to {:?}",
            self.mode,
            Mode::Next,
        );

        let next_move = self.next_move(direction);
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

    fn next_move(&mut self, direction: &Direction) -> Move {
        let state = self.get_and_move_state(direction);
        self.moves[state]
    }

    fn get_and_move_state(&mut self, direction: &Direction) -> usize {
        let state = self.state;
        if *direction == Direction::Forward {
            if state == 11 {
                self.state = 0;
            } else {
                self.state += 1;
            }
        } else if state == 0 {
            self.state = 11;
        } else {
            self.state -= 1;
        }

        state
    }

    fn swap(&mut self) {
        let tmp = self.current_root.clone();
        self.current_root = self.current_child.clone();
        self.current_child = tmp;
        // let old_x = x.0.replace(y.0.borrow().clone());
        // y.0.replace(old_x);
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

pub(crate) fn swap_partition(node: &SddRef, v: &VTreeRef, manager: &SddManager) -> Decision {
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
            let (fst_prime, fst_sub) = fst_element.get_prime_sub(&manager);
            let (snd_prime, snd_sub) = snd_element.get_prime_sub(&manager);

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
        manager::{options::SddOptions, SddManager},
        util::quick_draw,
    };

    use super::{Direction, Fragment};

    use pretty_assertions::assert_eq;

    #[test]
    fn fragment_forward() {
        // We should be able to create minimal right-linear fragment and visit all the
        // possible states while going forward.
        let manager = SddManager::new(SddOptions::default());

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

        quick_draw(&manager, &a_and_b_or_c, &format!("my_test_base"));
        for i in 0..=11 {
            let next_move = fragment.moves[fragment.state];
            // println!("\n... minimizing (state {} ~> {}, {next_move:?})", i, i + 1);
            fragment.next(&Direction::Forward, &manager);
            quick_draw(&manager, &a_and_b_or_c, &format!("my_test_{i}"));

            assert_eq!(
                models,
                manager.model_enumeration(&a_and_b_or_c),
                "{i}-th state failed after doing {next_move:?}",
            );
        }
    }
}
