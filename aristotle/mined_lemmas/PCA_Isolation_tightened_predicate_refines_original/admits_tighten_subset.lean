import Mathlib
import RequestProject.Main

/-!
# Set-theoretic denotation of isolation predicates

The Mathlib counterpart of `PCA.Isolation.tightened_predicate_refines_original`:
in terms of admitted state sets, refinement is set inclusion and tightening is
intersection, so the statement is exactly `Set.inter_subset_left`.
-/

namespace PCA.Isolation

/-- The set of states admitted by a predicate (its denotation). -/

theorem admits_tighten_subset {σ : Type*} (P Q : Pred σ) :
    admits (tighten P Q) ⊆ admits P := by
  rw [admits_tighten]
  exact Set.inter_subset_left

end PCA.Isolation

#print axioms PCA.Isolation.tightened_predicate_refines_original
#print axioms PCA.Isolation.admits_tighten_subset

/-!
# Tightened Predicate Refines Original
Category: Proof-Carrying Apps
Target: PCA.Isolation.tightened_predicate_refines_original
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u

/-- A *predicate* of the isolation engine: an admissibility test on engine states. -/
abbrev Pred (σ : Type u) := σ → Prop

/-- `P'` **refines** `P` when every state admitted by `P'` is admitted by `P`,
i.e. the refined predicate is at least as restrictive as the original. -/
