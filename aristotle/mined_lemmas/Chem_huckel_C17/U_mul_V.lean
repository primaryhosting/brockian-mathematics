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

open Polynomial Matrix

/-- The primitive 17-th root of unity `exp (2πi/17)`. -/

lemma U_mul_V : U * V = 1 := by
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm : ∀ k : Fin 17, U j k * V k l
      = (17 : ℂ)⁻¹ * (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ k.val := by
    intro k
    show zeta ^ (j.val * k.val) * ((17 : ℂ)⁻¹ * (zeta ^ (k.val * l.val))⁻¹) = _
    have e1 : zeta ^ (j.val * k.val) = (zeta ^ j.val) ^ k.val := by rw [pow_mul]
    have e2 : (zeta ^ (k.val * l.val))⁻¹ = ((zeta ^ l.val)⁻¹) ^ k.val := by
      rw [mul_comm, pow_mul, inv_pow]
    rw [e1, e2, mul_pow]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum, geom_sum_root j l]
  by_cases h : j = l
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    ring

