use crate::sdd::decision::Decision;

// TODO: Remove this struct completely?
#[derive(PartialEq, Eq, Clone)]
pub(crate) struct Node {
    decision: Decision,
}

impl Node {
    #[must_use]
    pub fn new(decision: Decision) -> Node {
        Node { decision }
    }
}
