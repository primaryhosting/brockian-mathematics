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

namespace Chem

open Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₄`, viewed with vertex set `ZMod 14`
(which is definitionally `Fin 14`). -/

lemma P_mul_Q : P * Q = 1 := by
  ext a b
  rw [Matrix.mul_apply]
  have : ∀ j : ZMod 14, P a j * Q j b = (14 : ℂ)⁻¹ * ch (j * (a - b)) := by
    intro j
    simp only [P, Q]
    rw [← mul_assoc, mul_comm (ch (a * j)) ((14:ℂ)⁻¹), mul_assoc, ← ch_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_ch]
  by_cases h : a = b
  · subst h; simp
  · have : a - b ≠ 0 := sub_ne_zero.mpr h
    simp [this, h]

