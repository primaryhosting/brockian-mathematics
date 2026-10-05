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

lemma cover (w : F) : w ∈ setA ∨ w ∈ setB ∨ w ∈ setC ∨ w ∈ setD := by
  by_cases hP : w ∈ PowA
  · exact Or.inl (Or.inr hP)
  cases hw : w.toWord with
  | nil =>
      exact absurd (show w ∈ PowA from ⟨0, by rw [hw]; rfl⟩) hP
  | cons q t =>
      obtain ⟨i, β⟩ := q
      have hhead : w.toWord.head? = some (i, β) := by rw [hw]; rfl
      fin_cases i <;> cases β
      · exact Or.inr (Or.inl ⟨show w.toWord.head? = _ from hhead, hP⟩)
      · exact Or.inl (Or.inl (show w.toWord.head? = _ from hhead))
      · exact Or.inr (Or.inr (Or.inr (show w.toWord.head? = _ from hhead)))
      · exact Or.inr (Or.inr (Or.inl (show w.toWord.head? = _ from hhead)))

