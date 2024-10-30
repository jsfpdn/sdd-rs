use crate::literal::{Literal, Polarity, Variable};

use bitvec::prelude::*;

pub struct Models {
    models: Vec<BitVec>,
    variables: Vec<Variable>,
}

impl Models {
    pub(crate) fn new(models: Vec<BitVec>, variables: Vec<Variable>) -> Self {
        Models { models, variables }
    }

    #[allow(unused)]
    pub(crate) fn all_models(&self) -> Vec<Model> {
        // TODO: Remove this once EnumerationIterator is implemented.
        self.models
            .iter()
            .map(|enumeration_bitvec| {
                Model::new_from_bitvector(enumeration_bitvec, &self.variables)
            })
            .collect()
    }
}

#[derive(Debug, PartialEq, Eq)]
pub struct Model {
    literals: Vec<Literal>,
}

impl Model {
    #[allow(unused)]
    pub(crate) fn new_from_literals(literals: Vec<Literal>) -> Self {
        Model { literals }
    }

    fn new_from_bitvector(model: &BitVec, labels: &[Variable]) -> Self {
        Model {
            literals: model
                .iter()
                .zip(labels.iter())
                .map(|(polarity, var_label)| {
                    Literal::new_with_label(Polarity::from(*polarity), var_label.clone())
                })
                .collect(),
        }
    }
}
