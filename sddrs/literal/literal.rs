use derive_more::derive::From;
use std::{convert::From, fmt::Display};

/// Index of a variable. This corresponds to the order in which
/// the variable was defined in [`crate::manager::SddManager`] during
/// initialization, not an SDD ID or vtree index.
#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug, Copy, Hash, From)]
pub(crate) struct VariableIdx(pub(crate) u32);

impl From<u16> for VariableIdx {
    fn from(value: u16) -> Self {
        VariableIdx(value.into())
    }
}

impl From<usize> for VariableIdx {
    fn from(value: usize) -> Self {
        VariableIdx(value.try_into().unwrap())
    }
}

/// Variable given by its name (label) and index.
#[derive(Eq, PartialEq, Debug, Clone, Hash)]
pub(crate) struct Variable {
    label: String,
    idx: VariableIdx,
}

impl Variable {
    #[must_use]
    pub fn new(v: &str, idx: u32) -> Variable {
        Variable {
            label: v.to_owned(),
            idx: VariableIdx(idx),
        }
    }

    /// Get the name (label) of a variable.
    #[must_use]
    pub fn label(&self) -> String {
        self.label.clone()
    }

    /// Get the index of a variable.
    pub(crate) fn index(&self) -> VariableIdx {
        self.idx
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.idx.cmp(&other.idx))
    }
}

impl Ord for Variable {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.idx.cmp(&other.idx)
    }
}

/// Polarity of a variable.
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
pub enum Polarity {
    Positive,
    Negative,
}

impl From<bool> for Polarity {
    fn from(item: bool) -> Self {
        if item {
            Polarity::Positive
        } else {
            Polarity::Negative
        }
    }
}

impl std::ops::Not for Polarity {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self {
            Polarity::Positive => Polarity::Negative,
            Polarity::Negative => Polarity::Positive,
        }
    }
}

/// Literal given by [`Variable`] and [`Polarity`].
#[derive(Eq, PartialEq, Debug, Clone, PartialOrd, Ord)]
pub(crate) struct Literal {
    variable: Variable,
    polarity: Polarity,
}

impl Literal {
    /// Create a new [`Literal`].
    #[allow(dead_code)]
    #[must_use]
    pub(crate) fn new(polarity: Polarity, variable: &str, idx: VariableIdx) -> Literal {
        Literal {
            variable: Variable::new(variable, idx.0),
            polarity,
        }
    }

    /// Create a new [`Literal`] from a [`Variable`].
    pub(crate) fn new_with_label(polarity: Polarity, variable: Variable) -> Literal {
        Literal { variable, polarity }
    }

    /// Check whether [`self`] is negated [`other`].
    #[must_use]
    pub(crate) fn eq_negated(&self, other: &Literal) -> bool {
        self.variable == other.variable && self.polarity != other.polarity
    }

    #[must_use]
    pub(crate) fn polarity(&self) -> Polarity {
        self.polarity
    }

    #[must_use]
    pub(crate) fn var_label(&self) -> Variable {
        self.variable.clone()
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let polarity = if self.polarity == Polarity::Positive {
            ""
        } else {
            "¬"
        };
        write!(f, "{}{}", polarity, self.variable.label)
    }
}
