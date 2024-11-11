use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    manager::SddManager,
    sdd::{Sdd, SddId, SddRef, SddType},
};

// Element node (a paired box) is a conjunction of prime and sub.
#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug, Copy)]
pub(crate) struct Element {
    pub(crate) prime: SddId,
    pub(crate) sub: SddId,
}

impl Element {
    pub(super) fn is_trimmed(&self, manager: &SddManager) -> bool {
        let (prime, sub) = self.get_prime_sub(manager);
        prime.is_trimmed(manager) && sub.is_trimmed(manager)
    }

    pub(super) fn is_compressed(&self, manager: &SddManager) -> bool {
        let (prime, sub) = self.get_prime_sub(manager);
        prime.is_compressed(manager) && sub.is_compressed(manager)
    }

    pub(crate) fn get_prime_sub<'a>(&self, manager: &'a SddManager) -> (SddRef, SddRef) {
        (manager.get_node(self.prime), manager.get_node(self.sub))
    }
}

impl Dot for Element {
    fn draw<'a>(&self, writer: &mut DotWriter, manager: &SddManager) {
        let idx = fxhash::hash(self);

        let (prime, sub) = self.get_prime_sub(manager);

        writer.add_node(
            idx,
            NodeType::Record(prime.0.borrow().dot_repr(), sub.0.borrow().dot_repr()),
        );

        if let Sdd {
            sdd_type: SddType::Decision(node),
            ..
        } = manager.get_node(self.prime).0.borrow().to_owned()
        {
            writer.add_edge(Edge::Prime(idx, fxhash::hash(&node)));
        }
        if let Sdd {
            sdd_type: SddType::Decision(node),
            ..
        } = manager.get_node(self.sub).0.borrow().to_owned()
        {
            writer.add_edge(Edge::Sub(idx, fxhash::hash(&node)));
        };
    }
}
