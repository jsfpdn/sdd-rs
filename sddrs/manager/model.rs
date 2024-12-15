//! Models of the compiled knowledge base.
use crate::literal::{Literal, Polarity, Variable};
use bitvec::prelude::*;
use std::fmt::Display;
use tabled::{builder::Builder, grid::config::HorizontalLine, settings::Theme};

/// All models of the knowledge base.
#[derive(Debug, PartialEq)]
pub struct Models {
    models: Vec<BitVec>,
    variables: Vec<Variable>,
}

impl Models {
    pub(crate) fn new(models: &[BitVec], variables: Vec<Variable>) -> Self {
        let mut models = models.to_owned();
        models.sort();
        Models { models, variables }
    }

    /// Get all models of the knowledge base.
    #[must_use]
    pub fn all_models(&self) -> Vec<Model> {
        self.models
            .iter()
            .map(|enumeration_bitvec| {
                Model::new_from_bitvector(enumeration_bitvec, &self.variables)
            })
            .collect()
    }
}

impl Display for Models {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut builder = Builder::default();
        builder.push_record(self.variables.iter().map(Variable::label));

        for model in &self.models {
            builder.push_record(
                model
                    .iter()
                    .map(|assignment| if *assignment { "1" } else { "0" }),
            );
        }

        let mut style = Theme::default();
        style.insert_horizontal_line(1, HorizontalLine::full('-', '-', ' ', ' '));
        let output = builder.build().with(style).to_string();
        write!(f, "{output}")
    }
}

/// Single model of the knowledge base. The model
/// is displayable.
#[derive(Debug, PartialEq, Eq)]
pub struct Model {
    literals: Vec<Literal>,
}

impl Model {
    #[allow(unused)]
    pub(crate) fn new_from_literals(literals: &[Literal]) -> Self {
        let mut literals = literals.to_owned();
        literals.sort();
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

impl Display for Model {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fn lit_repr(literal: &Literal) -> String {
            format!(
                "{}{literal}",
                if literal.polarity() == Polarity::Negative {
                    ""
                } else {
                    " "
                }
            )
        }

        write!(
            f,
            "{{{}}}",
            self.literals
                .iter()
                .map(lit_repr)
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
}
