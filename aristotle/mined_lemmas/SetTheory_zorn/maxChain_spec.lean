import Mathlib

/-!
# Zorn (Mathlib formulation)

Companion to `RequestProject/SetTheoryZorn.lean`.  That file is self-contained (it proves Zorn's

theorem maxChain_spec : IsMaxChain r (maxChain r) := by
  apply Classical.byContradiction
  intro h
  have hsuper := chainClosure_maxChain.isChain.superChain_succChain h
  exact hsuper.2.2 (chainClosure_maxChain.succ_fixpoint_iff.mpr rfl).symm

/-! ### Zorn's lemma -/

/-- **Zorn's lemma** for an arbitrary transitive relation: if every chain has an upper bound,
then there is a maximal element. -/
