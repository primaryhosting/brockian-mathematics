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

import Mathlib

/-!
# Rotations of three dimensional Euclidean space

Explicit rotations about the `z`- and `x`-axes, the cross product, and the fact that a
nontrivial rotation fixes at most two points of the unit sphere.
-/

open scoped RealInnerProductSpace

namespace BT

/-- Three dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- A vector of `E3` given by its three coordinates. -/

lemma disjoint_AB_CD : Disjoint (setA ∪ setB) (setC ∪ setD) := by
  rw [Set.disjoint_left]
  rintro w hw hw'
  simp only [setC, setD] at hw'
  have hw0 : w.toWord.head? = some (0, true) ∨ w.toWord.head? = some (0, false) := by
    rcases hw with (hw | hw) | ⟨hw, -⟩
    · exact Or.inl hw
    · rcases PowA_head hw with h | h
      · exfalso
        rcases hw' with hw' | hw' <;> rw [hw'] at h <;> simp at h
      · exact Or.inr h
    · exact Or.inr hw
  rcases hw' with hw' | hw' <;> rcases hw0 with h | h <;>
    rw [hw'] at h <;> exact absurd (Option.some_injective _ h) (by decide)

/-- The key identity `F = A ⊔ a • B`. -/
