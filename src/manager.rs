use std::collections::HashMap;

use crate::literal::VarLabelManager;
use crate::options::SddOptions;
use crate::sdd::Node;
use crate::vtree::VTreeManager;

#[allow(clippy::module_name_repetitions)]
pub struct SddManager<'a> {
    // TODO: Remove all #[allow(unused)] directives.
    #[allow(unused)]
    options: SddOptions,

    #[allow(unused)]
    vtree_manager: VTreeManager,

    #[allow(unused)]
    var_label_manager: VarLabelManager,

    // Unique table holding all the decision nodes.
    // More details can be found in [Algorithms and Data Structures in VLSI Design](https://link.springer.com/book/10.1007/978-3-642-58940-9).
    unqiue_table: HashMap<u64, Node<'a>>,
    // u64 is the hash of sdd::Decision
    // TODO: Should we store sdd::Decision or sdd::Node?
}

impl<'a> SddManager<'a> {
    #[must_use]
    pub fn new(options: SddOptions) -> SddManager<'a> {
        SddManager {
            options,
            vtree_manager: VTreeManager::new(),
            var_label_manager: VarLabelManager::new(),
            unqiue_table: HashMap::new(),
        }
    }

    #[must_use]
    pub fn new_with_nodes(options: SddOptions, nodes: HashMap<u64, Node<'a>>) -> SddManager {
        SddManager {
            options,
            vtree_manager: VTreeManager::new(),
            var_label_manager: VarLabelManager::new(),
            unqiue_table: nodes,
        }
    }

    #[must_use]
    pub fn get_node(&self, id: &u64) -> Option<&'a Node> {
        self.unqiue_table.get(id)
    }

    pub fn conjoin(&self, _fst: &Node, _snd: &Node) {}
    pub fn disjoin(&self, _fst: &Node, _snd: &Node) {}
    pub fn negate(&self, _fst: &Node) {}
    pub fn imply(&self, _fst: &Node, _snd: &Node) {}
    pub fn equiv(&self, _fst: &Node, _snd: &Node) {}

    pub fn condition() {}
    pub fn exist() {}
    pub fn forall() {}

    // TODO: expose operations manipulating the vtree.
}
