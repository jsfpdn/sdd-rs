use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::options::SDDOptions;
use crate::structs::{VarLabel, VarLabelManager};
use crate::vtree::{VTree, VTreeManager};

pub enum SDDNode {
    // TODO: Is `neg` in the original C library the same as `Reg` and `Compl` in rsdd?
    // TODO: Why is `Reg` and `Compl` defined in here in rsdd?
    False,
    True,
    Literal(VarLabel),
    Decision(SDDOr), // Decision node represents decomposition
}

// Decision node, disjunction of its elements
pub struct SDDOr {
    // TODO: In rsdd, SddOr contains also VTreeIndex (and a scratch field), do we need it as well?
    // TODO: Should `element` be a vector or a single SDDAnd node? Original C library uses a single node,
    // rsdd uses a vector. What's the difference?
    element: Vec<Rc<SDDAnd>>,

    // for GC
    ref_count: usize,
}
// Element node (a paired box), conjunction of prime and sub
pub struct SDDAnd {
    // prime, sub, both are either: ptr to decision node, constant (True or False) or a literal (X or !X)
    prime: Rc<SDDNode>,
    sub: Rc<SDDNode>,

    // for GC
    ref_count: usize,
}

pub struct SDDManager {
    options: SDDOptions,

    vtree_manager: VTreeManager,
    vtree_root: VTree,

    var_label_manager: VarLabelManager,

    nodes: HashMap<u64, SDDNode>,
}

impl SDDManager {
    #[must_use]
    pub fn new(options: SDDOptions) -> SDDManager {
        SDDManager {
            options,
            vtree_manager: VTreeManager::new(),
            vtree_root: VTree::new(None, None),
            var_label_manager: VarLabelManager::new(),
            nodes: HashMap::new(),
        }
    }

    pub fn conjoin() {}
    pub fn disjoin() {}
    pub fn negate() {}
    pub fn imply() {}
    pub fn equiv() {}

    pub fn condition() {}
    pub fn exist() {}
    pub fn forall() {}

    // TODO: expose operations manipulating the vtree.
}
