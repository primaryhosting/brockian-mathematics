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

lemma coverA (w : F) : w ∈ setA ∨ w ∈ ga • setB := by
  by_cases hA : w ∈ setA
  · exact Or.inl hA
  right
  have hnotSt : w.toWord.head? ≠ some (0, true) := fun h => hA (Or.inl h)
  have hnotPow : w ∉ PowA := fun h => hA (Or.inr h)
  refine ⟨ga⁻¹ * w, ⟨?_, ?_⟩, by simp⟩
  · -- `ga⁻¹ * w` starts with `(0, false)`
    have : (ga⁻¹ * w).toWord = ((0 : Fin 2), false) :: w.toWord := by
      rw [ga_inv_eq]
      refine toWord_letter_mul ?_
      rintro ⟨i, β⟩ hq hi
      simp only at hi
      subst hi
      cases β
      · rfl
      · exact absurd hq hnotSt
    rw [mem_St, this]
    simp
  · rintro ⟨n, hn⟩
    have hthis : (ga⁻¹ * w).toWord = ((0 : Fin 2), false) :: w.toWord := by
      rw [ga_inv_eq]
      refine toWord_letter_mul ?_
      rintro ⟨i, β⟩ hq hi
      simp only at hi
      subst hi
      cases β
      · rfl
      · exact absurd hq hnotSt
    rw [hthis] at hn
    cases n with
    | zero => simp at hn
    | succ m =>
        rw [List.replicate_succ] at hn
        exact hnotPow ⟨m, (List.cons.injEq _ _ _ _ ▸ hn).2⟩

