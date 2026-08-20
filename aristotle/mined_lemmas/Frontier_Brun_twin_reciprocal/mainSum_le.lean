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

lemma mainSum_le (x z k : ℕ) (hz : 3 ≤ z) :
    (twinSieve x z).mainSum (muPlus k) ≤
      4 / (Real.log z) ^ 2 + (1 / 2 : ℝ) ^ k * ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) := by
  have hsq := squarefree_bigP z
  -- termwise bound: truncation costs at most the tail `(1/2)^k * 4^ω(d)/d`
  have hterm : ∀ d ∈ (bigP z).divisors,
      muPlus k d * (twinSieve x z).nu d
        ≤ (ArithmeticFunction.moebius d : ℝ) * nu d + (1 / 2 : ℝ) ^ k * nuc 4 d := by
    intro d hd
    have hd0 : d ≠ 0 := by
      have := Nat.pos_of_mem_divisors hd; omega
    have hnu : (twinSieve x z).nu d = nu d := rfl
    have h4 : nuc 4 d = 2 ^ d.primeFactors.card * nu d := by
      rw [nuc_apply 4 hd0, nu_apply hd0, show (4:ℝ) = 2 * 2 by norm_num, mul_pow]
      ring
    have hnn := nu_nonneg d
    have hpow : (0:ℝ) ≤ (1 / 2 : ℝ) ^ k * nuc 4 d := by rw [h4]; positivity
    by_cases hk : d.primeFactors.card ≤ k
    · rw [hnu, muPlus, if_pos hk]
      linarith
    · rw [hnu, muPlus, if_neg hk, zero_mul]
      have hmu : (-1:ℝ) ≤ (ArithmeticFunction.moebius d : ℝ) :=
        neg_le_of_abs_le (abs_moebius_le_one d)
      have hbig : nu d ≤ (1 / 2 : ℝ) ^ k * nuc 4 d := by
        rw [h4]
        have h1 : (1:ℝ) ≤ (1 / 2 : ℝ) ^ k * 2 ^ d.primeFactors.card := by
          rw [div_pow, one_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity), one_mul, one_mul]
          exact pow_le_pow_right₀ (by norm_num) (by omega)
        nlinarith [hnn]
      nlinarith [hmu, hnn, hbig]
  -- the main term
  have hA : ∏ p ∈ (bigP z).primeFactors, (1 - nu p) ≤ 4 / (Real.log z) ^ 2 := by
    rw [primeFactors_bigP]
    have heq : ∀ p ∈ oddPrimesBelow z, (1 - nu p) = 1 - 2 / (p:ℝ) := fun p hp => by
      rw [nu_prime (prime_of_mem_oddPrimesBelow hp)]
    rw [Finset.prod_congr rfl heq]
    exact prod_odd_one_sub_two_div_le z hz
  -- the tail term
  have hB : ∏ p ∈ (bigP z).primeFactors, (1 + nuc 4 p)
      ≤ ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) := by
    rw [primeFactors_bigP]
    have heq : ∀ p ∈ oddPrimesBelow z, (1 + nuc 4 p) = 1 + 4 / (p:ℝ) := fun p hp => by
      rw [nuc_prime 4 (prime_of_mem_oddPrimesBelow hp)]
    rw [Finset.prod_congr rfl heq]
    have h2 : (2:ℕ) ∈ (z + 1).primesBelow :=
      Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
    have hprod := Finset.prod_erase_mul (z + 1).primesBelow (fun p => 1 + 4 / (p:ℝ)) h2
    have hnn : 0 ≤ ∏ p ∈ (z + 1).primesBelow.erase 2, (1 + 4 / (p:ℝ)) := by
      refine Finset.prod_nonneg fun p _ => ?_
      have : (0:ℝ) ≤ p := Nat.cast_nonneg p
      positivity
    rw [oddPrimesBelow, ← hprod]
    norm_num
    nlinarith [hnn]
  calc (twinSieve x z).mainSum (muPlus k)
      = ∑ d ∈ (bigP z).divisors, muPlus k d * (twinSieve x z).nu d := rfl
    _ ≤ ∑ d ∈ (bigP z).divisors,
          ((ArithmeticFunction.moebius d : ℝ) * nu d + (1 / 2 : ℝ) ^ k * nuc 4 d) :=
        Finset.sum_le_sum hterm
    _ = (∑ d ∈ (bigP z).divisors, (ArithmeticFunction.moebius d : ℝ) * nu d)
          + (1 / 2 : ℝ) ^ k * ∑ d ∈ (bigP z).divisors, nuc 4 d := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∏ p ∈ (bigP z).primeFactors, (1 - nu p))
          + (1 / 2 : ℝ) ^ k * ∏ p ∈ (bigP z).primeFactors, (1 + nuc 4 p) := by
        rw [ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree nu nu_mult
          hsq, (nuc_mult 4).prodPrimeFactors_one_add_of_squarefree hsq]
    _ ≤ 4 / (Real.log z) ^ 2 + (1 / 2 : ℝ) ^ k * ∏ p ∈ (z + 1).primesBelow, (1 + 4 / (p : ℝ)) := by
        gcongr

