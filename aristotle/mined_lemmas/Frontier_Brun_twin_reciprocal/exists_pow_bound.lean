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

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

theorem exists_pow_bound (a b : ℕ) : ∃ m₀ : ℕ, ∀ m ≥ m₀, a * (m + 2) ^ b ≤ 2 ^ m := by
  have h : (fun n : ℕ => ((n : ℝ)) ^ b) =o[Filter.atTop] fun n : ℕ => (2:ℝ) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt b (by norm_num)
  have hc : (0:ℝ) < 1 / (4 * a + 4) := by positivity
  have h2 := h.def hc
  rw [Filter.eventually_atTop] at h2
  obtain ⟨m₁, hm₁⟩ := h2
  refine ⟨m₁, fun m hm => ?_⟩
  have hthis := hm₁ (m + 2) (by omega)
  simp only [Real.norm_eq_abs] at hthis
  have h3 : ((m:ℝ) + 2) ^ b ≤ 1 / (4 * a + 4) * (4 * 2 ^ m) := by
    calc ((m:ℝ) + 2) ^ b = |(((m + 2 : ℕ) : ℝ)) ^ b| := by
          rw [abs_of_nonneg (by positivity)]; push_cast; ring
      _ ≤ 1 / (4 * a + 4) * |(2:ℝ) ^ (m + 2)| := hthis
      _ = 1 / (4 * a + 4) * (4 * 2 ^ m) := by
          rw [abs_of_nonneg (by positivity)]; ring
  have ha : (0:ℝ) ≤ a := by positivity
  have hpos : (0:ℝ) < 4 * (a:ℝ) + 4 := by positivity
  have h2m : (0:ℝ) < (2:ℝ) ^ m := by positivity
  have h5 := mul_le_mul_of_nonneg_left h3 ha
  have key : (a:ℝ) * (1 / (4 * a + 4) * (4 * 2 ^ m)) = (4 * a * 2 ^ m) / (4 * a + 4) := by
    field_simp
  rw [key, le_div_iff₀ hpos] at h5
  have hgoal : (a : ℝ) * ((m:ℝ) + 2) ^ b ≤ 2 ^ m := by nlinarith
  have hcast : ((a * (m + 2) ^ b : ℕ) : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast hcast

/-- Any fixed power of `log₂ N` is eventually at most `N`. -/
