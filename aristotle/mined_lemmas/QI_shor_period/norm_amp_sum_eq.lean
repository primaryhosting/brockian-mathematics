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

theorem norm_amp_sum_eq {Q r x0 y s : ℕ} {d : ℤ} (hQ : 0 < Q)
    (h : (r : ℤ) * y = s * Q + d) :
    ‖∑ j ∈ Finset.range (numTerms Q r x0),
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
          (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ))‖ =
      ‖∑ j ∈ Finset.range (numTerms Q r x0),
        Complex.exp ((((j : ℝ) * (2 * Real.pi * d / Q) : ℝ) : ℂ) * Complex.I)‖ := by
  have hQC : (Q : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hC : (r : ℂ) * y = s * Q + d := by exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h
  have key : ∀ j : ℕ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
      (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ))
      = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((x0 : ℂ) * y) / (Q : ℂ)) *
        Complex.exp ((((j : ℝ) * (2 * Real.pi * d / Q) : ℝ) : ℂ) * Complex.I) := by
    intro j
    rw [← Complex.exp_add]
    have hshift : 2 * (Real.pi : ℂ) * Complex.I *
          (((x0 : ℂ) + (j : ℂ) * (r : ℂ)) * (y : ℂ)) / (Q : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I * ((x0 : ℂ) * y) / (Q : ℂ) +
            (((j : ℝ) * (2 * Real.pi * d / Q) : ℝ) : ℂ) * Complex.I)
          + ((j * s : ℤ) : ℂ) * (2 * (Real.pi:ℂ) * Complex.I) := by
      push_cast
      field_simp
      linear_combination (j:ℂ) * hC
    rw [hshift, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [key, ← Finset.mul_sum, norm_mul, Complex.norm_exp]
  have hre : (2 * (Real.pi : ℂ) * Complex.I * ((x0 : ℂ) * y) / (Q : ℂ)).re = 0 := by
    simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
  rw [hre]
  simp

/-- Main analytic estimate: an outcome `y` whose phase `r y` is within `r/2` of a multiple
of `Q` is observed with probability at least `1/(6r)`. -/
