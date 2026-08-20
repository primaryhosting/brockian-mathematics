/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: this module is deliberately import-free (Lean 4 core only), because the
-- required header comment must be the very first thing in the file and Lean does
-- not permit an `import` after a module docstring.  The development below is the
-- predicate-level mirror of the set-level statement `Set.inter_subset_left` in
-- Mathlib (`(p ∩ g) ⊆ p`), which is the library lemma that closes the set-valued
-- form of the main theorem; see `RequestProject/IsolationSet.lean`.

namespace PCA.Isolation

universe u

variable {State : Type u}

/-- A predicate on the state space of the isolation engine. -/
abbrev Pred (State : Type u) := State → Prop

/-- `Refines q p` says that the predicate `q` is at least as strong as `p`: every
state accepted by `q` is accepted by `p`. -/

theorem tightenSet_eq_tighten (p g : Set State) :
    tightenSet p g = {s | tighten (· ∈ p) (· ∈ g) s} := rfl

/-- The predicate-level soundness theorem, read back from the set-level one. -/
