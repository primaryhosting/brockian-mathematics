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

theorem exists_prod_one_add_bound :
    ∃ (C : ℝ) (A : ℕ), 0 < C ∧ ∀ z : ℕ, 3 ≤ z →
      ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) ≤ C * (Real.log z) ^ A := by
  refine ⟨Real.exp 16 / (Real.log 2) ^ 16, 16, by positivity, fun z hz => ?_⟩
  set J := Nat.log 2 z with hJ
  have hJ1 : 1 ≤ J := by
    rw [hJ, Nat.one_le_iff_ne_zero, Ne, Nat.log_eq_zero_iff]
    push_neg
    exact ⟨by omega, by norm_num⟩
  have hJR : (1:ℝ) ≤ J := by exact_mod_cast hJ1
  -- `∏ (1 + 4/p) ≤ exp (∑ 4/p)`
  have hprodexp : ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
    · have : (0:ℝ) ≤ 4 / p := by positivity
      linarith
    · have := Real.add_one_le_exp (4 / (p:ℝ))
      linarith
  have hsum : ∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)
      ≤ 16 * (1 + Real.log J) := by
    have h := sum_inv_primesBelow_le z
    have heq : ∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)
        = 4 * ∑ p ∈ (z + 1).primesBelow, (1:ℝ) / p := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => by ring
    rw [heq]
    linarith
  have hexpmono := Real.exp_le_exp.mpr hsum
  have hval : Real.exp (16 * (1 + Real.log J)) = Real.exp 16 * (J : ℝ) ^ 16 := by
    have hJpos : (0:ℝ) < J := by linarith
    rw [mul_add, mul_one, Real.exp_add]
    congr 1
    rw [show (16:ℝ) = ((16:ℕ):ℝ) by norm_num, Real.exp_nat_mul, Real.exp_log hJpos]
  -- `J log 2 ≤ log z`
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hJlog : (J : ℝ) * Real.log 2 ≤ Real.log z := by
    have h1 : (2:ℝ) ^ J ≤ (z : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h2 : Real.log ((2:ℝ) ^ J) ≤ Real.log z :=
      Real.log_le_log (by positivity) h1
    rwa [Real.log_pow] at h2
  have hJle : (J : ℝ) ≤ Real.log z / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; exact hJlog
  calc ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ))
      ≤ Real.exp (∑ p ∈ (z + 1).primesBelow, 4 / (p : ℝ)) := hprodexp
    _ ≤ Real.exp (16 * (1 + Real.log J)) := hexpmono
    _ = Real.exp 16 * (J : ℝ) ^ 16 := hval
    _ ≤ Real.exp 16 * (Real.log z / Real.log 2) ^ 16 := by
        gcongr
    _ = Real.exp 16 / (Real.log 2) ^ 16 * (Real.log z) ^ 16 := by
        rw [div_pow]; ring

end Brun

import Mathlib

/-!
# Bonferroni / Brun's truncated Möbius weights

We show that truncating the Möbius function to arguments with at most `k` distinct prime
factors, where `k` is even, yields an upper bound sieve in the sense of
`BoundingSieve.IsUpperMoebius`.
-/

open Finset

namespace Brun

/-- Brun's truncated Möbius weights: `μ(d)` if `d` has at most `k` distinct prime factors,
and `0` otherwise. -/
