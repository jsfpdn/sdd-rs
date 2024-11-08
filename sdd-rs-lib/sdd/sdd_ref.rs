use crate::manager::SddManager;
use crate::sdd::Sdd;
use crate::sdd::SddType;

use bitvec::prelude::*;
use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SddRef(pub(crate) Rc<RefCell<Sdd>>);

impl SddRef {
    pub(crate) fn new(sdd: Sdd) -> Self {
        // TODO: Check that this gets called only from manager while maintaining the index.
        SddRef(Rc::new(RefCell::new(sdd)))
    }

    pub fn vtree_idx(&self) -> u16 {
        self.0.borrow().vtree_idx
    }

    pub fn id(&self) -> usize {
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
    pub fn eq_negated(&self, other: &SddRef, manager: &SddManager) -> bool {
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
        if let Some(negated_sdd_id) = self.0.borrow().negation {
            return manager
                .get_node(negated_sdd_id)
                .expect("Negation has been already computed and the SDD must therefore exist");
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
}
