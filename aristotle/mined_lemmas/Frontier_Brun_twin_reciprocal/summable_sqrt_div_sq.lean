import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma summable_sqrt_div_sq : Summable (fun m : ℕ => Real.sqrt m / (m : ℝ) ^ 2) := by
  have h : ∀ m : ℕ, Real.sqrt m / (m : ℝ) ^ 2 = 1 / (m : ℝ) ^ ((3 : ℝ) / 2) := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      have h2 : ((m : ℝ) ^ (2 : ℕ)) = (m : ℝ) ^ ((2 : ℝ)) := by
        rw [← Real.rpow_natCast (m : ℝ) 2]; norm_num
      rw [Real.sqrt_eq_rpow, h2, ← Real.rpow_sub hm0,
        show (1 : ℝ) / 2 - 2 = -((3 : ℝ) / 2) by ring, Real.rpow_neg hm0.le]
      simp
  simp only [h]
  rw [Real.summable_one_div_nat_rpow]
  norm_num

