use std::{any::Any, collections::BTreeSet};

use crate::{
    literal::Literal,
    manager::SddManager,
    sdd::{Decision, Element, LeftDependence, RightDependence, Sdd, SddType},
    vtree::VTreeRef,
};

use super::Node;

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

impl Fragment {
    // TODO: implement iterator over fragment states.
    // TODO: think about limits & rolling back states.
    pub(crate) fn new(root: VTreeRef, child: VTreeRef) -> Self {
        let linearity;
        {
            let root = root.borrow();
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

    fn next(&mut self, direction: &Direction) {
        assert!(self.state <= 11);
        assert!(
            self.mode.can_transition(Mode::Next),
            "cannot transition from {:?} to {:?}",
            self.mode,
            Mode::Next,
        );

        // self.mode == Mode::Initial => construct_fragment_shadows
        let next_move = self.next_move();
        // make_vtree_move(next_mode, self.current_root, self.current_child, manager)
        //      success => update_state(...)
        //      failure => status = 0
        //
        // crucial:
        //      vtree_operations/op_left_rotate.c
        //      vtree_operations/op_right_rotate.c
        //      vtree_operations/op_swap.c (seems easiest?)
        unimplemented!()
    }

    fn goto(&mut self) {
        unimplemented!()
    }
    fn rewind(&mut self) {
        unimplemented!()
    }

    fn next_move(&self) -> Move {
        // sdd_vtree_rotate_left();
        // or sdd_vtree_rotate_right(), depending on the direction
        unimplemented!()
    }

    pub(crate) fn find_best_state(&mut self) {
        // iterate over all 12 states, find the best one and return it
        unimplemented!()
    }

    fn vtree_move(&mut self, next_move: &Move, manager: &SddManager) {
        match next_move {
            Move::SwapChild => self.swap_child(manager),
            Move::RightRotateRoot => self.right_rotate_root(manager),
            Move::LeftRotateChild => self.left_rotate_child(manager),
        }
    }

    fn swap_child(&mut self, manager: &SddManager) {}

    fn right_rotate_root(&mut self, manager: &SddManager) {}

    fn left_rotate_child(&mut self, manager: &SddManager) {}
}

// TODO: How does rotation appear from outside?
// Does it invalidate everything? This seems the easiest. This would mean invalidating
// every SDD normalized for vtree reachable for the vtree we are rotating/swapping.
// => How does Sam represent OBDDs? Does he invalidate something or go the extra mile
//    when dynamically manipulate OBDDs under user's hands? (how does CUDD do it?)
//
// If it does not invalidate anything, we have to keep it in check somehow.
// How? Sdd could turn into Ref<Rc<Sdd>> but that would not work due to mutability.
// How does Sam do this with OBDDs? I suppose he manipulates OBDDs.
// => How does Sam compute id's of OBDDs? (how does CUDD do it?)
//
// SDD tainting. Also, by adjusting SDD normalized for a given vtree, not only everything below changes,
// but also everything above changes - we have to keep pointers (or indices?) to parents
// to be able to traverse up, change the elements (since the IDs of children have changed)
// but this will cause the id of the parent to change => recurse.
// (this problem could be explicitly mentioned in the thesis when describing the design if we choose
// to maintain parent pointers in SDDs).
// => Does Sam keep parent pointers in OBDDs? (Does CUDD keep them?)

// let a: SddRef = manager.literal("A", positive);
// let b: SddRef = manager.literal("B", positive);
// let a_and_b: SddRef = manager.conjoin(a, b);
//
//
// pub type SddRef = Rc<RefCell<SddRefInterned>>;
//
// struct SddRefInterned {
//    parent: usize,
//    sdd: Sdd
// }
//
// impl SddRefInterned {
//     fn id(&self) -> usize { self.sdd.id() }
// }
//
//
//

struct LeftRotateSplit {
    bc_vec: Vec<Sdd>,
    c_vec: Vec<Sdd>,
}

struct RightRotateSplit {
    ab_vec: Vec<Sdd>,
    a_vec: Vec<Sdd>,
}

/// Rotate the vtree `x` to the left and adjust SDDs accordingly.
///
/// ```ignore
///      w               x
///     / \             / \
///    a   x     ~>    w   c
///       / \         / \
///      b   c       a   b
/// ```
///
/// Children hanged at `w` must be split accordingly, depending on the vtrees
/// they are normalized for:
/// * `w(a, bc)` must be rotated and moved to `x` (~> `x(ab, c)`)
/// * `w(a, c)` must be moved to `x` (~> `x(a, c)`)
/// * `w(a, b)` stay at `w`
///
/// This is done by the [`split_nodes_for_left_rotate`] function.
fn sdd_vtree_rotate_left(x: &VTreeRef, manager: &SddManager) {
    // TODO: Move this to the SDDManager and make it public.
    let w = x
        .borrow()
        .get_parent()
        .expect("invalid fragment: `x` does not have a parent");

    let LeftRotateSplit { bc_vec, c_vec } = split_nodes_for_left_rotate(&w, x, manager);

    manager.rotate_vtree_left(x);

    for bc in &bc_vec {
        let elements = rotate_partition_left(bc, x, manager).elements;
        let new_node = Sdd::new(
            SddType::Decision(Decision { elements }),
            x.borrow().get_index(),
            None,
        );

        replace_node(bc, &new_node, manager);
    }

    unimplemented!()
    // TODO: Insert elements back into the unique_table (mimic finalize_vtree_op)
    // TODO: Garbage collection at the new root `x`.
}

fn sdd_vtree_rotate_right() {
    // TODO: Move this to the SDDManager and make it public.
    unimplemented!()

    // TODO: Insert elements back into the unique_table
    // TODO: Garbage collection
}

fn swap(fst: &Literal, snd: &Literal, manager: &SddManager) {
    // TODO: Move this to the SDDManager and make it public.
    // This is the same as sdd_vtree_rotate_{left, right}.
    unimplemented!()
}

fn replace_node(old: &Sdd, new: &Sdd, manager: &SddManager) {
    // TODO: Somehow replace bc with new.
    // This means recursively going up the SDD graph to the root and updating all
    // SDDs that have been "tainted"?
    unimplemented!()
}

/// Split SDDs in preparation for left rotation. See
/// [`sdd_vtree_rotate_left`] for more information.
///
/// This function removes split nodes from the unique table.
fn split_nodes_for_left_rotate(
    w: &VTreeRef,
    x: &VTreeRef,
    manager: &SddManager,
) -> LeftRotateSplit {
    let w_idx = w.borrow().get_index();

    // Collect all the SDDs which are normalized for `w`.
    let normalized_sdds = manager
        .get_nodes_normalized_for(w_idx)
        .iter()
        .map(|(id, sdd)| (sdd.dependence_on_right_vtree(x, manager), *id))
        .collect::<Vec<_>>();

    let mut c_vec = Vec::new();
    let mut bc_vec = Vec::new();

    for (dependence, id) in &normalized_sdds {
        if *dependence == RightDependence::B {
            continue;
        }

        let sdd = manager.get_node(*id).unwrap();
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

fn split_nodes_for_right_rotate(
    x: &VTreeRef,
    w: &VTreeRef,
    manager: &SddManager,
) -> RightRotateSplit {
    let x_idx = x.borrow().get_index();

    let normalized_sdds = manager
        .get_nodes_normalized_for(x_idx)
        .iter()
        .map(|(id, sdd)| (sdd.dependence_on_left_vtree(w, manager), *id))
        .collect::<Vec<_>>();

    let mut a_vec = Vec::new();
    let mut ab_vec = Vec::new();

    for (dependence, id) in &normalized_sdds {
        if *dependence == LeftDependence::B {
            continue;
        }

        let sdd = manager.get_node(*id).unwrap();
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

fn split_nodes_for_swap() {
    unimplemented!()
}

/// Rotate partitions to the left.
#[must_use]
fn rotate_partition_left(node: &Sdd, x: &VTreeRef, manager: &SddManager) -> Decision {
    // This function assumes that `x` has been already rotated and `w` is it's left child.
    let w = match x.borrow().node.clone() {
        Node::Internal(.., left_child) => left_child,
        Node::Leaf(..) => panic!("x must be an internal node, not a leaf"),
    };

    let x_idx = x.borrow().get_index();

    let SddType::Decision(ref decision) = node.sdd_type else {
        panic!("node must be a decision node");
    };

    let mut elements = BTreeSet::new();
    for element in &decision.elements {
        let (a, bc) = element.get_prime_sub(manager);

        if bc.is_constant() || bc.vtree_idx > x_idx {
            elements.insert(Element {
                prime: a.id(),
                sub: bc.id(),
            });
            continue;
        }

        if bc.vtree_idx == x_idx {
            let SddType::Decision(ref bc_decision) = bc.sdd_type else {
                panic!("node must be a decision node");
            };

            for bc_element in &bc_decision.elements {
                let (b, c) = bc_element.get_prime_sub(manager);
                // let ab = sdd_conjoin_lr(a, b, w, manager);
                // declare element (ab, c) for x
            }

            continue;
        }
        // bc is normalized for a vtree in b

        // TODO: Implement sdd_conjoin_lr
        // let ab = sdd_conjoin_lr(a, bc, w, manager);
        // declare element (ab, True) for x
        // let bc_neg = sdd_negate(bc, manager);
        // let ab = sdd_conjoin_lr(a, bc_neg, w, manager);
        //
        // declare_element (ab, False, x);
    }

    Decision { elements }.canonicalize(manager)
}

/// Rotate partitions to the right.
fn rotate_partition_right() {}
