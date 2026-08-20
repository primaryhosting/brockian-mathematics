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

lemma sum_inv_dyadic_block_le (z j : ℕ) (hj : 1 ≤ j) :
    ∑ p ∈ (z + 1).primesBelow.filter (fun p => Nat.log 2 p = j), (1 : ℝ) / p ≤ 4 / j := by
  set S := (z + 1).primesBelow.filter (fun p => Nat.log 2 p = j) with hS
  have hlow : ∀ p ∈ S, 2 ^ j ≤ p := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    have hpp := Nat.prime_of_mem_primesBelow hp.1
    have := Nat.pow_log_le_self 2 hpp.pos.ne'
    rwa [hp.2] at this
  have hcard := card_dyadic_block_mul_le z j
  have h1 : ∑ p ∈ S, (1 : ℝ) / p ≤ ∑ _p ∈ S, (1:ℝ) / 2 ^ j := by
    refine Finset.sum_le_sum fun p hp => ?_
    have := hlow p hp
    have h2 : (0:ℝ) < 2 ^ j := by positivity
    apply one_div_le_one_div_of_le h2
    exact_mod_cast this
  rw [Finset.sum_const, nsmul_eq_mul] at h1
  refine h1.trans ?_
  have hjR : (0:ℝ) < j := by exact_mod_cast hj
  have h2 : (0:ℝ) < 2 ^ j := by positivity
  have hc : (#S : ℝ) * j ≤ 2 ^ (j + 2) := by exact_mod_cast hcard
  have h4 : (2:ℝ) ^ (j + 2) = 4 * 2 ^ j := by ring
  rw [mul_one_div, div_le_div_iff₀ h2 hjR]
  linarith

/-- A weak Mertens estimate: `∑_{p ≤ z} 1/p ≤ 4 (1 + log (log₂ z))`. -/
