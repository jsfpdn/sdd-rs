use crate::sdd::decision::Decision;

#[derive(PartialEq, Eq, Clone, Hash)]
pub(crate) struct Node {
    decision: Decision,

    parents: u64,
    refs: u64,
    // TODO: Do we want field `parents: BTreeSet<u64>`? What would this point to? Since only the
    // decision nodes will be stored in the unique_table, then it would have to point to decision
    // node, not to the particular element pointing to it (since it is not hashed and stored
    // directly in the unique_table).
}

impl Node {
    #[must_use]
    pub fn new(decision: Decision) -> Node {
        Node {
            decision,
            parents: 0,
            refs: 0,
        }
    }
}
