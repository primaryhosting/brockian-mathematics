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

theorem prob_lower_bound {Q r x0 y s : ℕ} {d : ℤ} (hr : 0 < r) (hx0 : x0 < r)
    (hQ : 4 * r ^ 2 ≤ Q) (hd : 2 * |d| ≤ (r : ℤ)) (h : (r : ℤ) * y = s * Q + d) :
    1 / (6 * (r : ℝ)) ≤ prob Q r x0 y := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hr1 : 1 ≤ r := hr
  have hQr : 4 * r ≤ Q := by nlinarith
  have hx0Q : x0 < Q := by omega
  have hQpos : 0 < Q := by omega
  set m := numTerms Q r x0 with hmdef
  have hm : 0 < m := numTerms_pos hr hx0Q
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hQR : (0:ℝ) < Q := by exact_mod_cast hQpos
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr1
  have hQR2 : (4:ℝ) * (r:ℝ)^2 ≤ Q := by exact_mod_cast hQ
  have hmub : (m:ℝ) * r ≤ (Q:ℝ) + r - 1 := by
    have hnat := numTerms_mul_le (Q := Q) (r := r) (x0 := x0) hr hx0Q
    have h3 : ((x0 + m * r : ℕ) : ℝ) ≤ ((Q + r - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    have h4 : ((Q + r - 1 : ℕ) : ℝ) = (Q:ℝ) + r - 1 := by
      have h5 : 1 ≤ Q + r := by omega
      push_cast [Nat.cast_sub h5]
      ring
    push_cast at h3
    rw [h4] at h3
    linarith [Nat.cast_nonneg (α := ℝ) x0]
  have hmlb : (Q:ℝ) ≤ (r:ℝ) + (m:ℝ) * r := by
    have hnat := le_numTerms_mul (Q := Q) (r := r) (x0 := x0) hr
    have h3 : ((Q:ℕ) : ℝ) ≤ ((x0 + m * r : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at h3
    have hx : (x0:ℝ) ≤ r := by
      have hlt : (x0:ℝ) < r := by exact_mod_cast hx0
      linarith
    linarith
  set t : ℝ := 2 * Real.pi * d / Q with htdef
  have habst : |t| = 2 * Real.pi * |(d:ℝ)| / Q := by
    rw [htdef, abs_div, abs_of_pos hQR, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  have hdR : 2 * |(d:ℝ)| ≤ (r:ℝ) := by
    have hc : ((2 * |d| : ℤ) : ℝ) ≤ ((r:ℤ):ℝ) := by exact_mod_cast hd
    push_cast [Int.cast_abs] at hc
    linarith
  have hkey : (m:ℝ) * |t| ≤ 17 * Real.pi / 16 := by
    rw [habst]
    have h1 : (m:ℝ) * (2 * Real.pi * |(d:ℝ)| / Q) = 2 * Real.pi * ((m:ℝ) * |(d:ℝ)|) / Q := by
      field_simp
    rw [h1, div_le_iff₀ hQR]
    have hmd : (m:ℝ) * |(d:ℝ)| ≤ (m:ℝ) * r / 2 := by
      have hhalf : |(d:ℝ)| ≤ (r:ℝ)/2 := by linarith
      nlinarith
    have hQ2 : (16:ℝ) * ((r:ℝ) - 1) ≤ 4 * (r:ℝ)^2 := by nlinarith [sq_nonneg ((r:ℝ) - 2)]
    nlinarith
  have hgeom := norm_geom_sum_exp_lower m t hm hkey
  rw [prob_eq, norm_amp_sum_eq hQpos h, ← hmdef, ← htdef,
    le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ) * Q)]
  have hnn : (0:ℝ) ≤ ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ :=
    norm_nonneg _
  have hsq : ((m:ℝ)/2)^2 ≤
      ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖^2 := by
    nlinarith
  have hQ3 : 3 * (r:ℝ) ≤ Q := by nlinarith
  have hfinal : 1 / (6 * (r:ℝ)) * ((m:ℝ) * Q) ≤ ((m:ℝ)/2)^2 := by
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity : (0:ℝ) < 6 * (r:ℝ))]
    nlinarith
  linarith

/-! ## Correctness of the classical post-processing -/

/-- Two fractions with denominators at most `B` that are both within `1/(2B²)` of the same
real number are equal.  Hence the rational approximation step of Shor's algorithm has at
most one answer. -/
