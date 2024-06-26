use std::collections::{HashMap, HashSet};

use crate::{
    dot_writer::{Dot, DotWriter},
    literal::VarLabel,
    options::SddOptions,
    sdd::{Node, Sdd},
    vtree::VTreeManager,
    Result,
};

#[allow(clippy::module_name_repetitions)]
pub struct SddManager<'a> {
    // TODO: Remove all #[allow(unused)] directives.
    #[allow(unused)]
    options: SddOptions,

    #[allow(unused)]
    vtree_manager: VTreeManager,

    #[allow(unused)]
    var_labels: HashSet<VarLabel>,

    // Unique table holding all the decision nodes.
    // More details can be found in [Algorithms and Data Structures in VLSI Design](https://link.springer.com/book/10.1007/978-3-642-58940-9).
    unqiue_table: HashMap<usize, &'a Sdd<'a>>,
}

impl<'a> SddManager<'a> {
    #[must_use]
    pub fn new(options: SddOptions) -> SddManager<'a> {
        SddManager {
            options,
            vtree_manager: VTreeManager::new(),
            var_labels: HashSet::new(),
            unqiue_table: HashMap::new(),
        }
    }

    // TODO: This function should be removed as user should not be able to fill the unique_table
    // directly.
    #[must_use]
    pub fn new_with_nodes(options: SddOptions, sdds: &'a [&'a Sdd<'a>]) -> SddManager<'a> {
        let mut table = HashMap::new();
        for sdd in sdds {
            table.insert(sdd.id(), *sdd);
        }

        SddManager {
            options,
            vtree_manager: VTreeManager::new(),
            var_labels: HashSet::new(),
            unqiue_table: table,
        }
    }

    pub fn add_variable(&mut self, variable: VarLabel) {
        self.vtree_manager.add_variable(variable);
    }

    pub fn tautology(&self) {}
    pub fn contradiction(&self) {}

    /// # Panics
    /// Function panics if there is no such node with the corresponding id in the unique table.
    #[must_use]
    pub fn get_node(&self, id: usize) -> &'a Sdd {
        self.unqiue_table.get(&id).unwrap()
    }

    pub fn conjoin(&self, _fst: &Node, _snd: &Node) {}
    pub fn disjoin(&self, _fst: &Node, _snd: &Node) {}
    pub fn negate(&self, _fst: &Node) {}
    pub fn imply(&self, _fst: &Node, _snd: &Node) {}
    pub fn equiv(&self, _fst: &Node, _snd: &Node) {}

    pub fn condition() {}
    pub fn exist() {}
    pub fn forall() {}

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_sdd_graph(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        let mut dot_writer = DotWriter::new(String::from("sdd"));
        for node in self.unqiue_table.values() {
            node.draw(&mut dot_writer);
        }
        dot_writer.write(writer)
    }

    /// # Errors
    /// Returns an error if TBD.
    pub fn draw_vtree_graph(&self, writer: &mut dyn std::io::Write) -> Result<()> {
        let mut dot_writer = DotWriter::new(String::from("vtree"));
        self.vtree_manager.draw(&mut dot_writer);
        dot_writer.write(writer)
    }
    // TODO: expose operations manipulating the vtree.
}
