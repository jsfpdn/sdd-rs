#[derive(Hash, Eq, PartialEq, Debug, Copy, Clone, PartialOrd, Ord)]
pub struct VarLabel(u64);

impl VarLabel {
    #[must_use]
    pub fn new(v: u64) -> VarLabel {
        VarLabel(v)
    }
}

pub struct VarLabelManager {
    // TODO: bitset?, vector, hashmap?
}

impl VarLabelManager {
    #[must_use]
    pub fn new() -> VarLabelManager {
        VarLabelManager {}
    }
}

impl Default for VarLabelManager {
    #[must_use]
    fn default() -> Self {
        VarLabelManager::new()
    }
}

// Either true or false
#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy, PartialOrd, Ord)]
pub struct Literal {
    var_label: VarLabel,
    polarity: bool,
}

impl Literal {
    #[must_use]
    pub fn new(polarity: bool, var_label: VarLabel) -> Literal {
        Literal {
            var_label,
            polarity,
        }
    }

    #[must_use]
    pub fn negate(&self) -> Literal {
        Literal {
            var_label: VarLabel::new(self.var_label.0),
            polarity: !self.polarity,
        }
    }

    #[must_use]
    pub fn eq_negated(&self, other: &Literal) -> bool {
        self.var_label() == other.var_label() && self.polarity() != other.polarity()
    }

    #[must_use]
    pub fn polarity(self) -> bool {
        self.polarity
    }

    #[must_use]
    pub fn var_label(self) -> VarLabel {
        self.var_label
    }
}
