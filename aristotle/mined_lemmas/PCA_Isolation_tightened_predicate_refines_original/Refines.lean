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

theorem Refines.trans {σ : Type u} {P₁ P₂ P₃ : Pred σ}
    (h₁ : Refines P₁ P₂) (h₂ : Refines P₂ P₃) : Refines P₁ P₃ :=
  fun s h => h₂ s (h₁ s h)

/-- Tightening with the guard `Q` is idempotent up to refinement in the other
direction as well: the tightened predicate also refines the guard. -/
