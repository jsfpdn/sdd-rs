#[derive(Hash, Eq, PartialEq, Debug, Copy, Clone)]
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
#[derive(Hash, Eq, PartialEq, Debug, Clone, Copy)]
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
    pub fn negate(literal: &Literal) -> Literal {
        Literal {
            var_label: VarLabel::new(literal.var_label.0),
            polarity: !literal.polarity,
        }
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
