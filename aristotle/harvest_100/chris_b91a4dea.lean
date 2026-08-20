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
def Refines (q p : Pred State) : Prop := ∀ s, q s → p s

/-- Tightening a predicate `p` with an extra guard `g` (an additional side condition
imposed by the isolation engine). -/
def tighten (p g : Pred State) : Pred State := fun s => p s ∧ g s

/-- **Soundness of tightening.** The tightened predicate refines the original one:
every state accepted by `tighten p g` is accepted by `p`.  In Mathlib's set-valued
formulation this is exactly `Set.inter_subset_left`. -/
theorem tightened_predicate_refines_original (p g : Pred State) :
    Refines (tighten p g) p :=
  fun _ hs => hs.1

/-- The tightened predicate also refines the guard. -/
theorem tightened_predicate_refines_guard (p g : Pred State) :
    Refines (tighten p g) g :=
  fun _ hs => hs.2

/-- Refinement is reflexive. -/
theorem Refines.refl (p : Pred State) : Refines p p := fun _ hs => hs

/-- Refinement is transitive, so a chain of tightenings still refines the original. -/
theorem Refines.trans {r q p : Pred State} (h₁ : Refines r q) (h₂ : Refines q p) :
    Refines r p := fun s hs => h₂ s (h₁ s hs)

/-- Tightening is idempotent in the guard. -/
theorem tighten_tighten (p g : Pred State) :
    ∀ s, tighten (tighten p g) g s ↔ tighten p g s :=
  fun _ => ⟨fun h => h.1, fun h => ⟨h, h.2⟩⟩

/-- **Relative completeness of tightening.** If the guard is already implied by the
original predicate, then tightening loses nothing: the original predicate refines the
tightened one as well, so the two are equivalent. -/
theorem original_refines_tightened_of_implies {p g : Pred State} (h : ∀ s, p s → g s) :
    Refines p (tighten p g) :=
  fun s hs => ⟨hs, h s hs⟩

/-- Equivalence of the original and tightened predicates under the same hypothesis. -/
theorem tighten_iff_of_implies {p g : Pred State} (h : ∀ s, p s → g s) (s : State) :
    tighten p g s ↔ p s :=
  ⟨fun hs => hs.1, fun hs => ⟨hs, h s hs⟩⟩

/-- Iterated tightening by a list of guards still refines the original predicate. -/
theorem tightenList_refines_original :
    ∀ (gs : List (Pred State)) (p : Pred State), Refines (gs.foldl tighten p) p
  | [], _ => fun _ hs => hs
  | g :: gs, p => fun s hs =>
      tightened_predicate_refines_original p g s
        (tightenList_refines_original gs (tighten p g) s hs)

end PCA.Isolation

import Mathlib
import RequestProject.Isolation

/-!
# Set-valued form of "tightened predicate refines original"

The isolation engine's predicates, viewed as subsets of the state space.  Here the
main soundness statement is closed outright by the Mathlib lemma
`Set.inter_subset_left`.
-/

namespace PCA.Isolation

universe u

variable {State : Type u}

/-- Set-valued tightening: intersect the original predicate with the guard. -/
def tightenSet (p g : Set State) : Set State := p ∩ g

/-- **Soundness, set-valued form.** Closed by `Set.inter_subset_left`. -/
theorem tightenSet_subset_original (p g : Set State) : tightenSet p g ⊆ p :=
  Set.inter_subset_left

/-- The set-valued and predicate-valued formulations agree. -/
theorem tightenSet_eq_tighten (p g : Set State) :
    tightenSet p g = {s | tighten (· ∈ p) (· ∈ g) s} := rfl

/-- The predicate-level soundness theorem, read back from the set-level one. -/
theorem tightened_predicate_refines_original' (p g : Set State) :
    Refines (tighten (· ∈ p) (· ∈ g)) (· ∈ p) :=
  fun _ hs => tightenSet_subset_original p g hs

end PCA.Isolation

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

