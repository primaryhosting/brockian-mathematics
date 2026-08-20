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

theorem sum_exp_eq_zero (Q : ℕ) (c : ℤ) (hQ : 0 < Q) (hc : c ≠ 0) (hlt : |c| < Q) :
    ∑ y ∈ Finset.range Q, (Complex.exp (2 * (Real.pi:ℂ) * Complex.I * c / Q)) ^ y = 0 := by
  have hQC : (Q:ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hne : Complex.exp (2 * (Real.pi:ℂ) * Complex.I * c / Q) ≠ 1 := by
    intro hcon
    rw [Complex.exp_eq_one_iff] at hcon
    obtain ⟨n, hn⟩ := hcon
    have hpi : (Real.pi:ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact Real.pi_ne_zero
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    field_simp at hn
    have hz : c = Q * n := by exact_mod_cast hn
    rcases eq_or_ne n 0 with rfl | hn0
    · simp at hz; exact hc hz
    · have hge : (Q:ℤ) ≤ |c| := by
        rw [hz, abs_mul, abs_of_nonneg (by positivity : (0:ℤ) ≤ (Q:ℤ))]
        nlinarith [Int.one_le_abs hn0, (by positivity : (0:ℤ) ≤ (Q:ℤ))]
      omega
  rw [geom_sum_eq hne]
  have hpow : (Complex.exp (2 * (Real.pi:ℂ) * Complex.I * c / Q)) ^ Q = 1 := by
    rw [← Complex.exp_nat_mul]
    have hQr : (Q:ℂ) * (2 * (Real.pi:ℂ) * Complex.I * c / Q)
        = (c:ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by field_simp
    rw [hQr, Complex.exp_int_mul_two_pi_mul_I]
  rw [hpow]
  simp

/-- Orthogonality computation: the squared moduli of the Fourier amplitudes over the
progression `{x₀ + j r : j < m}` sum to `m Q`, provided the progression does not wrap
around (`|(j - k) r| < Q` for `j ≠ k`). -/
