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

lemma errSum_le (x z k : ℕ) (hz : 1 ≤ z) :
    (twinSieve x z).errSum (muPlus k) ≤ 2 * (2 * z : ℝ) ^ k := by
  have hterm : ∀ d ∈ (bigP z).divisors,
      |muPlus k d| * |BoundingSieve.rem (s := twinSieve x z) d|
        ≤ (if d.primeFactors.card ≤ k then 2 * (2:ℝ) ^ k else 0) := by
    intro d hd
    have hdvd : d ∣ bigP z := (Nat.mem_divisors.mp hd).1
    by_cases hk : d.primeFactors.card ≤ k
    · rw [if_pos hk]
      have h1 := abs_muPlus_le_one k d
      have h2 := abs_rem_le x z hdvd
      have h3 : (2:ℝ) ^ d.primeFactors.card ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
      calc |muPlus k d| * |BoundingSieve.rem (s := twinSieve x z) d|
          ≤ 1 * (2 * 2 ^ d.primeFactors.card) := mul_le_mul h1 h2 (abs_nonneg _) zero_le_one
        _ ≤ 2 * 2 ^ k := by rw [one_mul]; linarith
    · rw [if_neg hk]
      simp [muPlus, hk]
  have hdle : ∀ d ∈ (bigP z).divisors, d.primeFactors.card ≤ k → d ≤ z ^ k := by
    intro d hd hkd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hsq : Squarefree d := (squarefree_bigP z).squarefree_of_dvd hdvd
    have hpf : d.primeFactors ⊆ oddPrimesBelow z := by
      rw [← primeFactors_bigP z]
      exact Nat.primeFactors_mono hdvd (squarefree_bigP z).ne_zero
    calc d = ∏ p ∈ d.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq).symm
      _ ≤ ∏ _p ∈ d.primeFactors, z :=
          Finset.prod_le_prod' (fun p hp => (mem_oddPrimesBelow.mp (hpf hp)).2.2)
      _ = z ^ d.primeFactors.card := by rw [Finset.prod_const]
      _ ≤ z ^ k := Nat.pow_le_pow_right hz hkd
  have hcard : (((bigP z).divisors.filter (fun d => d.primeFactors.card ≤ k)).card : ℝ)
      ≤ (z:ℝ) ^ k := by
    have hsub : (bigP z).divisors.filter (fun d => d.primeFactors.card ≤ k)
        ⊆ Finset.Icc 1 (z ^ k) := by
      intro d hd
      rw [Finset.mem_filter] at hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hdle d hd.1 hd.2⟩
    have hle := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hle
    simp at hle
    exact_mod_cast hle
  rw [BoundingSieve.errSum]
  calc ∑ d ∈ (bigP z).divisors,
        |muPlus k d| * |BoundingSieve.rem (s := twinSieve x z) d|
      ≤ ∑ d ∈ (bigP z).divisors, (if d.primeFactors.card ≤ k then 2 * (2:ℝ) ^ k else 0) :=
        Finset.sum_le_sum hterm
    _ = 2 * (2:ℝ) ^ k * (((bigP z).divisors.filter (fun d => d.primeFactors.card ≤ k)).card : ℝ) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
        ring
    _ ≤ 2 * (2:ℝ) ^ k * (z:ℝ) ^ k := mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = 2 * (2 * z : ℝ) ^ k := by rw [mul_pow]; ring

/-- Brun's sieve bound for the number of twin primes up to `x`. -/
