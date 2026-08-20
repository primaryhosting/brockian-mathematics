/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QI

/-!
## Setting

We formalise the mathematical core of Shor's period–finding algorithm.

Fix a modulus `N`, an element `a` of order `r` modulo `N`, and a quantum register of
size `Q`.  Shor's algorithm prepares the uniform superposition
`Q^(-1/2) ∑_{x < Q} |x⟩ |a^x mod N⟩`, measures the second register — obtaining some value
`a^{x₀}` with `x₀ < r`, which collapses the first register to the uniform superposition over
the arithmetic progression `{x < Q : x ≡ x₀ [MOD r]}` — applies the quantum Fourier transform
of order `Q` to the first register and measures it.

The probability of observing the value `y` is therefore

  `prob Q r x₀ y = (m Q)⁻¹ * ‖∑_{j < m} exp(2πi (x₀ + j r) y / Q)‖²`,

where `m = numTerms Q r x₀` is the number of elements of the progression.  This is the
distribution `prob` defined below (`prob_sum_eq_one` verifies that it is a probability
distribution).

The theorems that constitute the correctness of the algorithm are:

* `QI.shor_period` : the measured value `y` lies, with probability at least
  `φ(r) / (6 r)`, in the set of outcomes from which the classical post-processing
  (best rational approximation with bounded denominator) returns the period `r`;
* `QI.shor_period_orderOf` : the same statement for `r = orderOf a`, i.e. for the period of
  the modular exponentiation function `x ↦ a ^ x`;
* `QI.recovers_unique` : that post-processing is well defined, i.e. an outcome `y`
  determines at most one period `r`;
* `QI.collapsed_register` : the set `{x < Q : a ^ x = a ^ x₀}` onto which the first register
  collapses is exactly the progression `{x₀ + j r : j < numTerms Q r x₀}`;
* `QI.prob_sum_eq_one` : `prob` is a probability distribution on the `Q` outcomes.
-/

/-- The number of `x < Q` with `x ≡ x₀ [MOD r]` and `x ≥ x₀`, i.e. `⌈(Q - x₀)/r⌉`. -/

theorem approx_unique {B p q p' q' : ℕ} {x : ℝ} (hq : 0 < q) (hqB : q ≤ B) (hq' : 0 < q')
    (hq'B : q' ≤ B) (hpq : Nat.Coprime q p) (hpq' : Nat.Coprime q' p')
    (h : |x - (p : ℝ) / q| < 1 / (2 * (B : ℝ) ^ 2))
    (h' : |x - (p' : ℝ) / q'| < 1 / (2 * (B : ℝ) ^ 2)) : p = p' ∧ q = q' := by
  have hqR : (0:ℝ) < q := by exact_mod_cast hq
  have hq'R : (0:ℝ) < q' := by exact_mod_cast hq'
  have hBR : (0:ℝ) < B := lt_of_lt_of_le hqR (by exact_mod_cast hqB)
  have hlt : |(p:ℝ)/q - (p':ℝ)/q'| < 1 / (B:ℝ)^2 := by
    have ht : |(p:ℝ)/q - (p':ℝ)/q'| ≤ |x - (p:ℝ)/q| + |x - (p':ℝ)/q'| := by
      have := abs_sub_le ((p:ℝ)/q) x ((p':ℝ)/q')
      rwa [abs_sub_comm ((p:ℝ)/q) x] at this
    have h2 : (1:ℝ)/(2*(B:ℝ)^2) + 1/(2*(B:ℝ)^2) = 1/(B:ℝ)^2 := by field_simp; ring
    linarith
  have hkey : (p:ℝ) * q' = p' * q := by
    by_contra hne
    have hne' : ((p:ℤ) * q' - p' * q) ≠ 0 := by
      intro h0
      apply hne
      have := congrArg (fun z : ℤ => (z:ℝ)) h0
      push_cast at this
      linarith
    have h1 : (1:ℝ) ≤ |(p:ℝ) * q' - (p':ℝ) * q| := by
      have h2 : (1:ℤ) ≤ |(p:ℤ) * q' - p' * q| := Int.one_le_abs (by omega)
      have h3 : ((1:ℤ):ℝ) ≤ ((|(p:ℤ) * q' - p' * q| : ℤ) : ℝ) := by exact_mod_cast h2
      rw [Int.cast_abs] at h3
      push_cast at h3
      simpa using h3
    have hdiff : |(p:ℝ)/q - (p':ℝ)/q'| = |(p:ℝ) * q' - (p':ℝ) * q| / ((q:ℝ) * q') := by
      rw [div_sub_div _ _ (ne_of_gt hqR) (ne_of_gt hq'R), abs_div,
        abs_of_pos (mul_pos hqR hq'R), mul_comm (q:ℝ) (p':ℝ)]
    have hqq : (q:ℝ) * q' ≤ (B:ℝ)^2 := by
      have h1 : (q:ℝ) ≤ B := by exact_mod_cast hqB
      have h2 : (q':ℝ) ≤ B := by exact_mod_cast hq'B
      nlinarith
    rw [hdiff, div_lt_iff₀ (mul_pos hqR hq'R)] at hlt
    have hle : (1:ℝ)/(B:ℝ)^2 * ((q:ℝ)*q') ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      exact hqq
    linarith
  have hnat : p * q' = p' * q := by exact_mod_cast hkey
  have hdvd : q ∣ q' := Nat.Coprime.dvd_of_dvd_mul_left hpq ⟨p', by rw [hnat]; ring⟩
  have hdvd' : q' ∣ q := Nat.Coprime.dvd_of_dvd_mul_left hpq' ⟨p, by rw [← hnat]; ring⟩
  have hqq : q = q' := Nat.dvd_antisymm hdvd hdvd'
  subst hqq
  exact ⟨Nat.eq_of_mul_eq_mul_right hq hnat, rfl⟩

/-- The post-processing is unambiguous: an outcome `y` determines at most one period. -/
