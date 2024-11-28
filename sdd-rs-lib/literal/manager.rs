use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap};

use crate::literal::{Polarity, Variable, VariableIdx};
use crate::sdd::SddRef;

#[derive(Clone, Debug)]
pub(crate) struct LiteralVariants {
    positive_literal: SddRef,
    negative_literal: SddRef,
}

impl LiteralVariants {
    pub(crate) fn get(&self, polarity: Polarity) -> SddRef {
        match polarity {
            Polarity::Positive => self.positive_literal.clone(),
            Polarity::Negative => self.negative_literal.clone(),
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

    pub(crate) fn add_variable(
        &self,
        variable: &Variable,
        positive_literal: SddRef,
        negative_literal: SddRef,
    ) {
        self.literals.borrow_mut().insert(
            variable.clone(),
            LiteralVariants {
                positive_literal,
                negative_literal,
            },
        );
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

    pub(crate) fn find_by_index(&self, index: VariableIdx) -> Option<(Variable, LiteralVariants)> {
        self.literals
            .borrow()
            .iter()
            .find(|(variable, _)| variable.index() == index)
            .map(|(variable, variants)| (variable.clone(), variants.clone()))
    }

    pub(crate) fn find_by_label(&self, label: &str) -> Option<(Variable, LiteralVariants)> {
        self.literals
            .borrow()
            .iter()
            .find(|(variable, _)| variable.label() == label)
            .map(|(variable, variants)| (variable.clone(), variants.clone()))
    }
}

#[cfg(test)]
mod test {
    use crate::literal::Polarity;
    use crate::manager::options::vars;
    use crate::manager::{options::SddOptions, SddManager};

    #[test]
    fn create_literals() {
        let options = SddOptions::builder()
            .variables(vars(vec!["a", "b"]))
            .build();
        let manager = SddManager::new(options);

        manager.literal("a", Polarity::Negative);
        manager.literal("a", Polarity::Positive);

        manager.literal("b", Polarity::Negative);
        manager.literal("b", Polarity::Positive);
    }
}
