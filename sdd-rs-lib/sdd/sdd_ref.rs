use crate::manager::{CachedOperation, SddManager};
use crate::sdd::{Sdd, SddId, SddType};
use crate::vtree::VTreeRef;
use bitvec::prelude::*;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::rc::Rc;

use super::Element;

#[derive(Debug, Clone)]
pub struct SddRef(pub(crate) Rc<RefCell<Sdd>>);

impl PartialEq for SddRef {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id()
    }
}

impl Eq for SddRef {}

impl SddRef {
    pub(crate) fn new(sdd: Sdd) -> Self {
        SddRef(Rc::new(RefCell::new(sdd)))
    }

    pub fn vtree(&self) -> VTreeRef {
        self.0.borrow().vtree.clone()
    }

    pub fn id(&self) -> SddId {
        self.0.borrow().id()
    }

    /// Check whether the SDD represent a true constant.
    pub fn is_true(&self) -> bool {
        self.0.borrow().is_true()
    }

    /// Check whether the SDD represent a false constant.
    pub fn is_false(&self) -> bool {
        self.0.borrow().is_false()
    }

    /// Check whether the SDD represents either the true or false constants.
    pub fn is_constant(&self) -> bool {
        self.is_true() || self.is_false()
    }

    /// Check whether the SDD represents a literal.
    pub fn is_literal(&self) -> bool {
        self.0.borrow().is_literal()
    }

    /// Check whether the SDD represents either a constant or literal.
    pub fn is_constant_or_literal(&self) -> bool {
        self.is_constant() || self.is_literal()
    }

    /// Check whether [`self`] equals to the negated [`other`].
    ///
    /// This operation may create more SDDs in the unique table.
    pub(crate) fn eq_negated(&self, other: &SddRef, manager: &SddManager) -> bool {
        if let Some(negation) = manager.get_cached_operation(CachedOperation::Neg(self.id())) {
            return negation == other.id();
        }

        // TODO: This may cause panic w.r.t. borrowing here and later when negating.
        let fst_sdd_type = self.0.borrow().sdd_type.clone();
        let snd_sdd_type = other.0.borrow().sdd_type.clone();

        match (fst_sdd_type, snd_sdd_type) {
            (SddType::True, SddType::False) | (SddType::False, SddType::True) => true,
            (SddType::Literal(fst), SddType::Literal(snd)) => fst.eq_negated(&snd),
            (SddType::Decision(..), SddType::Decision(..)) => {
                self.negate(manager).id() == other.id()
            }
            (_, _) => false,
        }
    }

    /// Negate the SDD and cache it.
    ///
    /// The computation works lazily - if the negation has been already computed,
    /// the value is just returned.
    pub(crate) fn negate(&self, manager: &SddManager) -> SddRef {
        if let Some(negation) = manager.get_cached_operation(CachedOperation::Neg(self.id())) {
            return manager.get_node(negation);
        }

        let negation = self.0.borrow_mut().negate(manager);
        manager.insert_node(&negation);
        negation
    }

    /// Return the models if they are already cached.
    pub(crate) fn models(&self) -> Option<Vec<BitVec>> {
        self.0.borrow().models.clone()
    }

    /// Return the number of models if they are already cached.
    pub(crate) fn model_count(&self) -> Option<u64> {
        self.0.borrow().model_count
    }

    pub(crate) fn cache_models(&self, models: &[BitVec]) {
        self.0.borrow_mut().models = Some(models.to_vec());
    }

    pub(crate) fn cache_model_count(&self, model_count: u64) {
        self.0.borrow_mut().model_count = Some(model_count);
    }

    pub(crate) fn canonicalize(&self, manager: &SddManager) {
        let canonicalized = self.0.borrow_mut().canonicalize(manager);
        let mut old = self.0.borrow_mut();
        *old = canonicalized;
    }

    /// Recursively check whether [`self`] and all its descendants are trimmed.
    /// SDD is trimmed if it does not contain decompositions in the form of
    /// `{(true, alpha)}` and `{(alpha, true), (!alpha, false)}`.
    pub fn is_trimmed(&self, manager: &SddManager) -> bool {
        self.0.borrow().is_trimmed(manager)
    }

    /// Recursivelly checks whether the SDD is compressed.
    /// Decision node is compressed if all subs are distinct, i.e.,
    /// for all indexes i,j such that i != j, it holds that `s_i != s_j`.
    ///
    /// See definition 8 in [SDD: A New Canonical Representation of Propositional Knowledge Bases](https://ai.dmi.unibas.ch/research/reading_group/darwiche-ijcai2011.pdf).
    ///
    /// # Panics
    /// Function panics if
    /// * elements are not stored in the SDD manager,
    /// * the decision node contains something else than boxed elements.
    pub fn is_compressed(&self, manager: &SddManager) -> bool {
        self.0.borrow().is_compressed(manager)
    }

    pub(crate) fn replace_contents(&self, other: SddType) {
        self.0.borrow_mut().sdd_type = other;
    }

    pub(crate) fn set_vtree(&self, vtree: VTreeRef) {
        self.0.borrow_mut().vtree = vtree;
    }

    pub(crate) fn elements(&self) -> Option<BTreeSet<Element>> {
        match self.0.borrow().sdd_type {
            SddType::Decision(ref decision) => Some(decision.elements.clone()),
            _ => None,
        }
    }
}
