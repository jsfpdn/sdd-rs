use crate::{
    dot_writer::{Dot, DotWriter, Edge, NodeType},
    manager::SddManager,
    sdd::{Sdd, SddId, SddRef, SddType},
};

// Element node (a paired box) is a conjunction of prime and sub.
#[derive(PartialEq, Eq, Clone, Debug)]
pub(crate) struct Element {
    pub(crate) prime: SddRef,
    pub(crate) sub: SddRef,
}

impl PartialOrd for Element {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Element {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        let order = self.prime.id().cmp(&other.prime.id());
        if order == std::cmp::Ordering::Equal {
            self.sub.id().cmp(&other.sub.id())
        } else {
            order
        }
    }
}

impl Element {
    pub(super) fn is_trimmed(&self, manager: &SddManager) -> bool {
        let (prime, sub) = self.get_prime_sub();
        prime.is_trimmed(manager) && sub.is_trimmed(manager)
    }

    pub(super) fn is_compressed(&self, manager: &SddManager) -> bool {
        let (prime, sub) = self.get_prime_sub();
        prime.is_compressed(manager) && sub.is_compressed(manager)
    }

    pub(crate) fn get_prime_sub(&self) -> (SddRef, SddRef) {
        (self.prime.clone(), self.sub.clone())
    }

    pub(crate) fn hash(&self) -> usize {
        #[derive(Hash)]
        struct PrimeSub {
            prime: SddId,
            sub: SddId,
        }

        fxhash::hash(&PrimeSub {
            prime: self.prime.id(),
            sub: self.sub.id(),
        })
    }
}

impl Dot for Element {
    fn draw<'a>(&self, writer: &mut DotWriter) {
        // TODO: Remove unused manager.
        let idx = self.hash();
        let (prime, sub) = self.get_prime_sub();

        writer.add_node(
            idx,
            NodeType::Record(prime.0.borrow().dot_repr(), sub.0.borrow().dot_repr()),
        );

        if let Sdd {
            sdd_type: SddType::Decision(node),
            ..
        } = self.prime.0.borrow().to_owned()
        {
            writer.add_edge(Edge::Prime(idx, node.hash()));
        }
        if let Sdd {
            sdd_type: SddType::Decision(node),
            ..
        } = self.sub.0.borrow().to_owned()
        {
            writer.add_edge(Edge::Sub(idx, node.hash()));
        };
    }
}
