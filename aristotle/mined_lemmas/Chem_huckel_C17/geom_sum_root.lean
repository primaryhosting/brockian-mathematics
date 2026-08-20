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

lemma geom_sum_root (j l : Fin 17) :
    ∑ k : Fin 17, (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ k.val
      = if j = l then (17 : ℂ) else 0 := by
  have hpow17 : ∀ m : ℕ, (zeta ^ m) ^ 17 = 1 := by
    intro m
    rw [← pow_mul, mul_comm, pow_mul, zeta_pow_17, one_pow]
  rw [Fin.sum_univ_eq_sum_range (fun i => (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ i) 17]
  by_cases h : j = l
  · subst h
    rw [mul_inv_cancel₀ (zeta_pow_val_ne_zero j)]
    simp
  · have hr1 : zeta ^ j.val * (zeta ^ l.val)⁻¹ ≠ 1 := by
      intro hcon
      have h2 : zeta ^ j.val = zeta ^ l.val := by
        have h3 := congrArg (fun x : ℂ => x * zeta ^ l.val) hcon
        simpa [mul_assoc, inv_mul_cancel₀ (zeta_pow_val_ne_zero l)] using h3
      exact h (Fin.ext (zeta_primitiveRoot.pow_inj j.isLt l.isLt h2))
    have h17 : (zeta ^ j.val * (zeta ^ l.val)⁻¹) ^ 17 = 1 := by
      rw [mul_pow, hpow17, inv_pow, hpow17, inv_one, mul_one]
    have hgeom := geom_sum_mul (zeta ^ j.val * (zeta ^ l.val)⁻¹) 17
    rw [h17, sub_self] at hgeom
    rcases mul_eq_zero.1 hgeom with h1 | h2
    · rw [if_neg h]
      exact h1
    · exact absurd (sub_eq_zero.1 h2) hr1

