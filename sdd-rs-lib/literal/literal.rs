use derive_more::derive::From;
use std::{convert::From, fmt::Display};

#[derive(PartialEq, Eq, Clone, PartialOrd, Ord, Debug, Copy, Hash, From)]
pub(crate) struct VariableIdx(pub(crate) u32);

impl From<u16> for VariableIdx {
    fn from(value: u16) -> Self {
        VariableIdx(value as u32)
    }
}

impl From<usize> for VariableIdx {
    fn from(value: usize) -> Self {
        VariableIdx(value.try_into().unwrap())
    }
}

#[derive(Eq, PartialEq, Debug, Clone, Ord, Hash)]
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

    #[must_use]
    pub fn label(&self) -> String {
        self.label.clone()
    }

    pub(crate) fn index(&self) -> VariableIdx {
        self.idx
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.idx.cmp(&other.idx))
    }
}

// Either true or false
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

#[derive(Eq, PartialEq, Debug, Clone, PartialOrd, Ord)]
pub struct Literal {
    variable: Variable,
    polarity: Polarity,
}

impl Literal {
    #[must_use]
    pub fn new(polarity: Polarity, variable: &str, idx: VariableIdx) -> Literal {
        // TODO: Get rid of this public constructor
        Literal {
            variable: Variable::new(variable, idx.0),
            polarity,
        }
    }

    pub(crate) fn new_with_label(polarity: Polarity, variable: Variable) -> Literal {
        Literal { variable, polarity }
    }

    #[must_use]
    pub fn negate(&self) -> Literal {
        Literal {
            variable: self.variable.clone(),
            polarity: !self.polarity,
        }
    }

    #[must_use]
    pub fn eq_negated(&self, other: &Literal) -> bool {
        self.variable == other.variable && self.polarity != other.polarity
    }

    #[must_use]
    pub fn polarity(&self) -> Polarity {
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
            "!"
        };
        write!(f, "{}{}", polarity, self.variable.label)
    }
}
