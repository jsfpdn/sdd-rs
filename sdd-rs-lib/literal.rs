use std::fmt::Display;

#[derive(Hash, Eq, PartialEq, Debug, Clone, PartialOrd, Ord)]
pub struct VarLabel(String);

impl VarLabel {
    #[must_use]
    pub fn new(v: &str) -> VarLabel {
        VarLabel(v.to_owned())
    }

    #[must_use]
    pub fn str(&self) -> String {
        self.0.clone()
    }
}

// Either true or false
#[derive(Hash, Eq, PartialEq, Debug, Clone, PartialOrd, Ord)]
pub struct Literal {
    var_label: VarLabel,
    polarity: Polarity,
}

#[derive(Hash, Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Copy)]
pub enum Polarity {
    Positive,
    Negative,
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

impl Literal {
    #[must_use]
    pub fn new(polarity: Polarity, var_label: VarLabel) -> Literal {
        Literal {
            var_label,
            polarity,
        }
    }

    #[must_use]
    pub fn negate(&self) -> Literal {
        Literal {
            var_label: VarLabel::new(&self.var_label.0),
            polarity: !self.polarity,
        }
    }

    #[must_use]
    pub fn eq_negated(&self, other: &Literal) -> bool {
        self.var_label == other.var_label && self.polarity != other.polarity
    }

    #[must_use]
    pub fn polarity(self) -> Polarity {
        self.polarity
    }

    #[must_use]
    pub fn var_label(self) -> VarLabel {
        self.var_label
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let polarity = if self.polarity == Polarity::Positive {
            ""
        } else {
            "!"
        };
        write!(f, "{}{}", polarity, self.var_label.0)
    }
}
