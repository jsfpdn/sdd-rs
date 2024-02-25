use std::collections::HashMap;

use crate::literal::VarLabelManager;
use crate::options::SddOptions;
use crate::sdd::Node;
use crate::sdd::Sdd;
use crate::vtree::VTreeManager;

#[allow(clippy::module_name_repetitions)]
pub struct SddManager {
    options: SddOptions,

    vtree_manager: VTreeManager,

    var_label_manager: VarLabelManager,

    nodes: HashMap<u64, Node>,
}

impl SddManager {
    #[must_use]
    pub fn new(options: SddOptions) -> SddManager {
        SddManager {
            options,
            vtree_manager: VTreeManager::new(),
            var_label_manager: VarLabelManager::new(),
            nodes: HashMap::new(),
        }
    }

    #[must_use]
    pub fn new_with_nodes(options: SddOptions, nodes: HashMap<u64, Node>) -> SddManager {
        SddManager {
            options,
            vtree_manager: VTreeManager::new(),
            var_label_manager: VarLabelManager::new(),
            nodes,
        }
    }

    #[must_use]
    pub fn get_node(&self, id: &u64) -> Option<&Node> {
        self.nodes.get(id)
    }

    pub fn conjoin(&self, _fst: &Sdd, _snd: &Sdd) {}
    pub fn disjoin(&self, _fst: &Sdd, _snd: &Sdd) {}
    pub fn negate(&self, _fst: &Sdd) {}
    pub fn imply(&self, _fst: &Sdd, _snd: &Sdd) {}
    pub fn equiv(&self, _fst: &Sdd, _snd: &Sdd) {}

    pub fn condition() {}
    pub fn exist() {}
    pub fn forall() {}

    // TODO: expose operations manipulating the vtree.
}
