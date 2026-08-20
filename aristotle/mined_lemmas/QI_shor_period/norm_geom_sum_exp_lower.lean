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

theorem norm_geom_sum_exp_lower (m : ℕ) (t : ℝ) (hm : 0 < m) (ht : (m : ℝ) * |t| ≤ 17 * Real.pi / 16) :
    (m : ℝ) / 2 ≤ ‖∑ j ∈ Finset.range m, Complex.exp ((((j : ℝ) * t : ℝ) : ℂ) * Complex.I)‖ := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  rcases eq_or_ne t 0 with rfl | htne
  · simp
  have habs : (0:ℝ) < |t| := abs_pos.2 htne
  have hlet : |t| ≤ (m:ℝ) * |t| := le_mul_of_one_le_left habs.le hm1
  have hthalf : |t / 2| ≤ 17 * Real.pi / 32 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hsin : Real.sin (t/2) ≠ 0 := by
    intro h0
    have h1 : |Real.sin (t/2)| = Real.sin |t/2| := abs_sin_eq_sin_abs (by nlinarith)
    rw [h0] at h1
    simp at h1
    have hpos : 0 < Real.sin |t/2| := Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith)
    rw [← h1] at hpos
    exact lt_irrefl _ hpos
  rw [norm_geom_sum_exp m t hsin]
  have e1 : |Real.sin (t/2)| = Real.sin (|t|/2) := by
    rw [abs_sin_eq_sin_abs (by nlinarith), abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have e2 : |Real.sin ((m:ℝ) * t/2)| = Real.sin ((m:ℝ) * |t|/2) := by
    rw [abs_sin_eq_sin_abs, abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul,
      abs_of_nonneg (le_of_lt hmR)]
    · rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_mul,
        abs_of_nonneg (le_of_lt hmR)]
      linarith
  rw [e1, e2]
  have hu : 0 < |t|/2 := by positivity
  have hupi : |t|/2 < Real.pi := by linarith
  have hsinu : 0 < Real.sin (|t|/2) := Real.sin_pos_of_pos_of_lt_pi hu hupi
  rw [le_div_iff₀ hsinu]
  have hle : Real.sin (|t|/2) ≤ |t|/2 := Real.sin_le (le_of_lt hu)
  have hhalf := half_le_sin (a := (m:ℝ) * |t|/2) (by positivity) (by linarith)
  nlinarith

/-! ## Elementary facts about `numTerms` -/

