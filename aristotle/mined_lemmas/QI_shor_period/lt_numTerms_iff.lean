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

theorem lt_numTerms_iff {Q r x0 j : ℕ} (hr : 0 < r) (hx0 : x0 < Q) :
    j < numTerms Q r x0 ↔ x0 + j * r < Q := by
  have h1 := le_numTerms_mul (Q := Q) (r := r) (x0 := x0) hr
  have h2 := numTerms_mul_le (Q := Q) (r := r) (x0 := x0) hr hx0
  constructor
  · intro hj
    have hle : j * r ≤ (numTerms Q r x0 - 1) * r := Nat.mul_le_mul_right r (by omega)
    have h3 : (numTerms Q r x0 - 1) * r + r = numTerms Q r x0 * r := by
      have h4 : 1 ≤ numTerms Q r x0 := by omega
      cases' Nat.exists_eq_add_of_le h4 with c hc
      rw [hc]; simp; ring
    omega
  · intro hj
    by_contra hcon
    push_neg at hcon
    have : numTerms Q r x0 * r ≤ j * r := Nat.mul_le_mul_right r hcon
    omega

/-! ## The collapsed register is an arithmetic progression

Measuring the second register of `Q^(-1/2) ∑_{x < Q} |x⟩ |a^x⟩` returns some value `a^{x₀}`
with `x₀ < r = orderOf a`, and collapses the first register to the uniform superposition
over `{x < Q : a^x = a^{x₀}}`.  That set is exactly the arithmetic progression
`{x₀ + j r : j < numTerms Q r x₀}` used in the definition of `amp`. -/

