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

lemma poly_le_geom (A : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, (t : ℝ) ^ A ≤ C * 2 ^ t := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) ^ A * (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_const_mul_const_pow_of_abs_lt_one A (by norm_num)
  obtain ⟨C, hC⟩ := h.bddAbove_range
  refine ⟨max C 1, by positivity, fun t => ?_⟩
  have ht : (t : ℝ) ^ A * (1 / 2 : ℝ) ^ t ≤ C := hC ⟨t, rfl⟩
  have hpow : ((1 : ℝ) / 2) ^ t * 2 ^ t = 1 := by rw [← mul_pow]; norm_num
  have hrw : (t : ℝ) ^ A = ((t : ℝ) ^ A * (1 / 2 : ℝ) ^ t) * 2 ^ t := by
    rw [mul_assoc, hpow, mul_one]
  rw [hrw]
  exact mul_le_mul_of_nonneg_right (le_trans ht (le_max_left _ _)) (by positivity)

