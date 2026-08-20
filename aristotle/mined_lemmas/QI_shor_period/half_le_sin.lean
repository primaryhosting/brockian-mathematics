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

theorem half_le_sin {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 17 * Real.pi / 32) : a / 2 ≤ Real.sin a := by
  have hpi1 : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  rcases le_total a (Real.pi / 2) with hc | hc
  · have hms := Real.mul_le_sin h0 hc
    have h4 : a / 2 ≤ 2 / Real.pi * a := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith : (0:ℝ) < Real.pi)]
      nlinarith
    linarith
  · have hs : Real.sin a = Real.cos (a - Real.pi / 2) := by
      rw [← Real.cos_pi_div_two_sub, ← Real.cos_neg]
      ring_nf
    have hb : 0 ≤ a - Real.pi / 2 := by linarith
    have hb2 : a - Real.pi / 2 ≤ Real.pi / 32 := by linarith
    have hcos := Real.one_sub_sq_div_two_le_cos (x := a - Real.pi / 2)
    nlinarith

/-- Closed form for the modulus of a geometric sum of unit phases. -/
