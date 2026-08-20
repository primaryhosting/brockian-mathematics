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

theorem tighten_iff {σ : Type u} (P Q : Pred σ) (s : σ) :
    tighten P Q s ↔ (P s ∧ Q s) := Iff.rfl

/-- Refinement is reflexive. -/
