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

theorem admits_tighten {σ : Type*} (P Q : Pred σ) :
    admits (tighten P Q) = admits P ∩ admits Q := rfl

/-- The admitted set of the tightened predicate is contained in that of the original;
this is Mathlib's `Set.inter_subset_left`. -/
