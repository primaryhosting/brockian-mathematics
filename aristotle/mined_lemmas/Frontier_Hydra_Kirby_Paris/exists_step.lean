import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem exists_step (h : Hydra) : h = .node [] ∨ ∃ h', Step h h' := by
  refine Hydra.rec (motive_1 := fun u => u = .node [] ∨ ∃ u', Step u u')
    (motive_2 := fun l => l = [] ∨ ∃ l', Step (Hydra.node l) (Hydra.node l')) ?_ ?_ ?_ h
  · rintro l (rfl | ⟨l', hl'⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨_, hl'⟩
  · exact Or.inl rfl
  · rintro u t (rfl | ⟨u', hu'⟩) _
    · exact Or.inr ⟨t, Step.root [] t⟩
    · exact Or.inr ⟨u' :: t, Step.deep [] t u u' hu'⟩

/-- Example of a move: cutting the single head of the hydra `•—•—•` makes the hydra grow
five new heads at the root. -/
example : Step (.node [.node [.node []]]) (.node (List.replicate 5 (.node []))) :=
  Step.copy [] [] [] [] 5

/-- The move relation of the hydra game is well-founded. -/
