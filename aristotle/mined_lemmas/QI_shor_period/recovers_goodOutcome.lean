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

theorem recovers_goodOutcome {Q r B s : ℕ} (hr : 0 < r) (hrB : r ≤ B) (hQ : 4 * B ^ 2 ≤ Q)
    (hs : Nat.Coprime r s) : Recovers B Q r (goodOutcome Q r s) := by
  have hB : 0 < B := lt_of_lt_of_le hr hrB
  have hQpos : 0 < Q := by nlinarith
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hBR : (0:ℝ) < B := by exact_mod_cast hB
  refine ⟨hr, hrB, s, hs, ?_⟩
  set y := goodOutcome Q r s with hy
  have hd := goodOutcome_spec (Q := Q) (r := r) (s := s) hr
  rw [← hy] at hd
  have key : (y:ℝ)/Q - (s:ℝ)/r = ((r:ℝ) * y - (s:ℝ) * Q) / ((r:ℝ) * Q) := by field_simp
  have habs : |(r:ℝ) * y - (s:ℝ) * Q| ≤ (r:ℝ)/2 := by
    have h2 : ((2 * |(r : ℤ) * (y:ℤ) - (s:ℤ) * Q| : ℤ) : ℝ) ≤ ((r:ℤ):ℝ) := by exact_mod_cast hd
    push_cast [Int.cast_abs] at h2
    linarith
  rw [key, abs_div, abs_of_pos (by positivity : (0:ℝ) < (r:ℝ) * Q)]
  have hQB : (4:ℝ) * (B:ℝ)^2 ≤ Q := by exact_mod_cast hQ
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [habs, sq_nonneg ((B:ℝ))]

/-! ## The distribution is a probability distribution -/

