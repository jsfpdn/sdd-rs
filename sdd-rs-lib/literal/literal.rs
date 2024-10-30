use std::{convert::From, fmt::Display};

#[derive(Hash, Eq, PartialEq, Debug, Clone, Ord)]
pub(crate) struct Variable {
    label: String,
    idx: u16,
}

impl Variable {
    #[must_use]
    pub fn new(v: &str, idx: u16) -> Variable {
        Variable {
            label: v.to_owned(),
            idx,
        }
    }

    #[must_use]
    pub fn label(&self) -> String {
        self.label.clone()
    }

    pub(crate) fn index(&self) -> u16 {
        self.idx
    }
}

impl PartialOrd for Variable {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.idx.cmp(&other.idx))
    }
}

// Either true or false
#[derive(Hash, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
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

#[derive(Hash, Eq, PartialEq, Debug, Clone, PartialOrd, Ord)]
pub struct Literal {
    variable: Variable,
    polarity: Polarity,
}

impl Literal {
    #[must_use]
    pub fn new(polarity: Polarity, variable: &str, idx: u16) -> Literal {
        // TODO: Get rid of this public constructor
        Literal {
            variable: Variable::new(variable, idx),
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
