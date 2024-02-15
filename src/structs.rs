pub struct VarLabel {
    // TODO: uint64, int64 or String?
    // uint64: rsdd (=> varset)
    // int64: original c library (=> negation of variable with index X represented as -X)
    // ?String: biodivine-lib-bdd?

    // can be true or false
}

impl VarLabel {
    pub fn new() -> VarLabel {
        VarLabel {}
    }
}

pub struct VarLabelManager {
    // TODO: bitset?, vector, hashmap?
}

impl VarLabelManager {
    pub fn new() -> VarLabelManager {
        VarLabelManager {}
    }
}

// Either true or false
pub struct Literal {
    var_label: VarLabel,
    polarity: bool,
}

impl Literal {
    pub fn new(polarity: bool, var_label: VarLabel) -> Literal {
        Literal {
            var_label,
            polarity,
        }
    }
}
