pub struct VarLabel {
    // TODO: uint64, int64 or String?
    // uint64: rsdd (=> varset)
    // int64: original c library (=> negation of variable with index X represented as -X)
    // ?String: biodivine-lib-bdd?

    // can be true or false
}

impl VarLabel {
    #[must_use]
    pub fn new() -> VarLabel {
        VarLabel {}
    }
}

impl Default for VarLabel {
    #[must_use]
    fn default() -> Self {
        VarLabel::new()
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
}
