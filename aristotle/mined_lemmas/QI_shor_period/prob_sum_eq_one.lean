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

theorem prob_sum_eq_one {Q r x0 : ℕ} (hr : 0 < r) (hx0 : x0 < Q) :
    ∑ y ∈ Finset.range Q, prob Q r x0 y = 1 := by
  have hQpos : 0 < Q := by omega
  set m := numTerms Q r x0 with hmdef
  have hm : 0 < m := numTerms_pos hr hx0
  have hmr : (m:ℤ) * r ≤ (Q:ℤ) + r - 1 := by
    have hnat := numTerms_mul_le (Q := Q) (r := r) (x0 := x0) hr hx0
    have h1 : ((x0 + m * r : ℕ) : ℤ) ≤ ((Q + r - 1 : ℕ) : ℤ) := by exact_mod_cast hnat
    have h2 : ((Q + r - 1 : ℕ) : ℤ) = (Q:ℤ) + r - 1 := by
      have h3 : 1 ≤ Q + r := by omega
      push_cast [Nat.cast_sub h3]
      ring
    push_cast at h1
    rw [h2] at h1
    linarith [Int.natCast_nonneg x0]
  have hspread : ∀ j k : ℕ, j < m → k < m → j ≠ k → |((j:ℤ) - k) * (r:ℤ)| < Q := by
    intro j k hj hk hjk
    have hjk' : |((j:ℤ) - k)| ≤ (m:ℤ) - 1 := by rw [abs_le]; omega
    have hrZ : (0:ℤ) < r := by exact_mod_cast hr
    rw [abs_mul, abs_of_pos hrZ]
    nlinarith
  have hsum : ∑ y ∈ Finset.range Q, prob Q r x0 y =
      (∑ y ∈ Finset.range Q, ‖∑ j ∈ Finset.range m,
        Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (j:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))‖^2)
        / ((m:ℝ) * Q) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun y _ => prob_eq)
  rw [hsum, sum_norm_sq_geom Q r x0 m hQpos hr hspread, div_self]
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQpos
  positivity

/-! ## Main theorem -/

/-- **Shor's period finding.**  Let `r ≥ 1` be the period of the modular exponentiation
function `x ↦ a^x mod N`, let `B ≥ r` be a bound on the period known in advance and let the
quantum register size satisfy `Q ≥ 4B²`.  Whatever the outcome `x₀ < r` of the measurement of
the second register, the probability that the measured value `y` of the first register
determines the period (i.e. that the classical continued–fraction post-processing with
denominator bound `B` returns `r`) is at least `φ(r)/(6r)`. -/
