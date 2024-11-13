use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};

use crate::literal::{Literal, Polarity, Variable, VariableIdx};
use crate::sdd::{Sdd, SddId, SddRef, SddType};
use crate::vtree::{VTreeIdx, VTreeManager};

#[derive(Clone, Debug)]
struct LiteralVariants {
    positive_literal: Option<SddRef>,
    negative_literal: Option<SddRef>,
}

impl LiteralVariants {
    fn get(&self, polarity: Polarity) -> Option<SddRef> {
        match polarity {
            Polarity::Positive => self.positive_literal.clone(),
            Polarity::Negative => self.negative_literal.clone(),
        }
    }

    fn insert(&mut self, sdd: SddRef) {
        let polarity = {
            match sdd.0.borrow().sdd_type {
                SddType::Literal(ref literal) => literal.polarity(),
                _ => unreachable!(),
            }
        };

        match polarity {
            Polarity::Positive => {
                assert!(self.positive_literal.is_none());
                self.positive_literal = Some(sdd);
            }
            Polarity::Negative => {
                assert!(self.negative_literal.is_none());
                self.negative_literal = Some(sdd);
            }
        }
    }
}

#[derive(Debug)]
pub(crate) struct LiteralManager {
    literals: RefCell<HashMap<Variable, LiteralVariants>>,
}

impl LiteralManager {
    pub(crate) fn new() -> Self {
        LiteralManager {
            literals: RefCell::new(HashMap::new()),
        }
    }

    pub(crate) fn new_literal(
        &self,
        label: &str,
        polarity: Polarity,
        next_sdd_idx: SddId,
        vtree_manager: &mut VTreeManager,
    ) -> (SddRef, bool) {
        let variable = match self.find_by_label(label) {
            None => {
                let variable = Variable::new(label, self.literals.borrow().len() as u32);
                vtree_manager.add_variable(&variable);
                variable
            }
            Some((variable, variants)) => {
                // Either positive or negative literal has been already constructed,
                // if it was, return it.
                if let Some(sdd) = variants.get(polarity) {
                    return (sdd, false);
                }
                variable
            }
        };

        // SddRef has not been constructed yet, we need to create it now and add it to the HashMap.
        let literal = Literal::new_with_label(polarity, variable.clone());
        let vtree_idx = vtree_manager.get_variable_vtree(&variable).unwrap().index();

        (self.create_sdd_ref(literal, next_sdd_idx, vtree_idx), true)
    }

    pub(crate) fn new_literal_from_idx(
        &self,
        variable_idx: VariableIdx,
        next_sdd_idx: SddId,
        polarity: Polarity,
        vtree_manager: &mut VTreeManager,
    ) -> (SddRef, bool) {
        let variable = self
            .literals
            .borrow()
            .iter()
            .find(|(variable, _)| variable.index() == variable_idx)
            .map(|(variable, _)| variable)
            .cloned()
            .unwrap();

        self.new_literal(&variable.label(), polarity, next_sdd_idx, vtree_manager)
    }

    pub(crate) fn len(&self) -> usize {
        self.literals.borrow().len()
    }

    pub(crate) fn all_variables(&self) -> BTreeSet<Variable> {
        self.literals
            .borrow()
            .iter()
            .map(|(variable, _)| variable)
            .cloned()
            .collect()
    }

    pub(crate) fn exists(&self, variable: &Variable) -> bool {
        self.literals.borrow().contains_key(variable)
    }

    fn find_by_label(&self, label: &str) -> Option<(Variable, LiteralVariants)> {
        self.literals
            .borrow()
            .iter()
            .find(|(variable, _)| variable.label() == label)
            .map(|(variable, variants)| (variable.clone(), variants.clone()))
    }

    fn create_sdd_ref(&self, literal: Literal, sdd_idx: SddId, vtree_idx: VTreeIdx) -> SddRef {
        let sdd = SddRef::new(Sdd::new(
            SddType::Literal(literal.clone()),
            sdd_idx,
            vtree_idx,
            None,
        ));

        let variants = match self.find_by_label(&literal.var_label().label()) {
            Some((_, variants)) => variants,
            _ => LiteralVariants {
                positive_literal: None,
                negative_literal: None,
            },
        };

        let mut variants = variants.clone();
        variants.insert(sdd.clone());

        self.literals
            .borrow_mut()
            .insert(literal.var_label(), variants);

        sdd
    }
}

#[cfg(test)]
mod test {
    use crate::literal::Polarity;
    use crate::manager::{options::SddOptions, SddManager};

    #[test]
    fn create_literals() {
        let manager = SddManager::new(SddOptions::default());
        manager.literal("a", Polarity::Negative);
        manager.literal("a", Polarity::Positive);

        manager.literal("b", Polarity::Negative);
        manager.literal("b", Polarity::Positive);
    }
}
