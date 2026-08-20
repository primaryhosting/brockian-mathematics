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

def admits {σ : Type*} (P : Pred σ) : Set σ := {s | P s}

/-- Refinement is inclusion of admitted sets. -/

def Refines {σ : Type u} (P' P : Pred σ) : Prop := ∀ s, P' s → P s

/-- Tightening a predicate `P` with an extra guard `Q`: a state is admitted by the
tightened predicate exactly when it passes both the original policy and the guard. -/

def tighten {σ : Type u} (P Q : Pred σ) : Pred σ := fun s => P s ∧ Q s

/-- **Main theorem.** The tightened predicate refines the original one: adding a guard
can only shrink the admitted set of states, never enlarge it.  The proof is the core
lemma `And.left` (whose Mathlib set-level counterpart is `Set.inter_subset_left`). -/

theorem tightened_predicate_refines_original {σ : Type u} (P Q : Pred σ) :
    Refines (tighten P Q) P :=
  fun _ h => h.1

/-- **Soundness and completeness** of the tightening construction: the tightened
predicate admits precisely those states admitted by the original predicate that
additionally satisfy the guard. -/

theorem Refines.refl {σ : Type u} (P : Pred σ) : Refines P P := fun _ h => h

/-- Refinement is transitive. -/

theorem Refines.trans {σ : Type u} {P₁ P₂ P₃ : Pred σ}
    (h₁ : Refines P₁ P₂) (h₂ : Refines P₂ P₃) : Refines P₁ P₃ :=
  fun s h => h₂ s (h₁ s h)

/-- Tightening with the guard `Q` is idempotent up to refinement in the other
direction as well: the tightened predicate also refines the guard. -/
