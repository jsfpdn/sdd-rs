use crate::{
    literal::Literal,
    manager::{SddManager, FALSE_SDD_IDX, TRUE_SDD_IDX},
    sdd::{Decision, Element, SddRef, SddType},
    vtree::{Node, VTreeRef},
};
use std::collections::{self, BTreeSet};

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
    // TODO: Add counts: IC, IR, Ic
    root: VTreeRef,
    child: VTreeRef,

    current_root: VTreeRef,
    current_child: VTreeRef,

    state: usize,
    mode: Mode,
    linearity: Linearity,
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
    pub(crate) fn new(root: VTreeRef, child: VTreeRef) -> Self {
        let linearity;
        {
            let root = root.0.borrow();
            if let Node::Internal(lc, rc) = &root.node {
                if *lc == child {
                    linearity = Linearity::Left;
                } else if *rc == child {
                    linearity = Linearity::Right;
                } else {
                    panic!("'child' must be direct child of 'root'")
                }
            } else {
                panic!("'root' must be a leaf")
            }
        }

        Fragment {
            root: root.clone(),
            child: child.clone(),
            current_root: root,
            current_child: child,
            linearity,
            state: 0,
            mode: Mode::Initial,
        }
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
    let w_idx = w.index();

    // Collect all the SDDs which are normalized for `w`.
    let normalized_sdds = manager
        .get_nodes_normalized_for(w_idx)
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
    // This function assumes that `x` has been already rotated and `w` is it's left child.
    let SddType::Decision(ref decision) = node.0.borrow().sdd_type else {
        panic!("node must be a decision node");
    };

    let mut elements = BTreeSet::new();
    for element in &decision.elements {
        let (a, bc) = element.get_prime_sub(manager);

        if bc.is_constant() || bc.vtree_idx() > x.index() {
            elements.insert(Element {
                prime: a.id(),
                sub: bc.id(),
            });
            continue;
        }

        if bc.vtree_idx() == x.index() {
            let SddType::Decision(ref bc_decision) = bc.0.borrow().sdd_type else {
                panic!("node must be a decision node");
            };

            for bc_element in &bc_decision.elements {
                let (b, c) = bc_element.get_prime_sub(manager);
                // TODO: Once conjoin is able to do vtree search on it's own, turn it off in here.
                // TODO: we could improve this since we already know LCA, which is x's left child.
                let ab = manager.conjoin(&a, &b);
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
            prime: manager.conjoin(&a, &bc).id(),
            sub: TRUE_SDD_IDX,
        });

        // Create element (a && !bc, False).
        elements.insert(Element {
            prime: manager.conjoin(&a, &manager.negate(&bc)).id(),
            sub: FALSE_SDD_IDX,
        });
    }

    Decision { elements }.canonicalize(manager)
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
        let (ab, c) = element.get_prime_sub(manager);

        if ab.vtree_idx() >= x.inorder_first() && ab.vtree_idx() <= x.inorder_last() {
            elements.insert(Element {
                prime: TRUE_SDD_IDX,
                sub: manager.conjoin(&ab, &c).id(),
            });

            continue;
        }

        if ab.vtree_idx() == w.index() {
            let SddType::Decision(ref ab_decision) = ab.0.borrow().sdd_type else {
                panic!("node must be a decision node");
            };

            for ab_element in &ab_decision.elements {
                let (a, b) = ab_element.get_prime_sub(manager);
                let bc = manager.conjoin(&b, &c);
                elements.insert(Element {
                    prime: a.id(),
                    sub: bc.id(),
                });
            }

            continue;
        }

        elements.insert(Element {
            prime: ab.id(),
            sub: c.id(),
        });

        elements.insert(Element {
            prime: manager.negate(&ab).id(),
            sub: FALSE_SDD_IDX,
        });
    }

    Decision { elements }.canonicalize(manager)
}

pub(crate) fn swap_partition(node: &SddRef, v: &VTreeRef, manager: &SddManager) -> Decision {
    let SddType::Decision(ref decision) = node.0.borrow().sdd_type else {
        panic!("node must be a decision node");
    };

    let mut elements = BTreeSet::new();
    for element in &decision.elements {
        let (a, b) = element.get_prime_sub(manager);
        if !b.is_false() {
            elements.insert(Element {
                prime: b.id(),
                sub: a.id(),
            });
        }

        let neg_b = manager.negate(&b);
        if !neg_b.is_false() {
            elements.insert(Element {
                prime: neg_b.id(),
                sub: FALSE_SDD_IDX,
            });
        }
    }

    Decision { elements }.canonicalize(manager)
}
