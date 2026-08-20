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

theorem sum_norm_sq_geom (Q r x0 m : ℕ) (hQ : 0 < Q) (hr : 0 < r)
    (hspread : ∀ j k : ℕ, j < m → k < m → j ≠ k → |((j:ℤ) - k) * r| < Q) :
    ∑ y ∈ Finset.range Q, ‖∑ j ∈ Finset.range m,
      Complex.exp (2 * (Real.pi:ℂ) * Complex.I * (((x0:ℂ) + (j:ℂ) * (r:ℂ)) * (y:ℂ)) / (Q:ℂ))‖ ^ 2
      = (m:ℝ) * Q := by
  have hQC : (Q:ℂ) ≠ 0 := by simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hrZ : (r:ℤ) ≠ 0 := by positivity
  have hC : ((∑ y ∈ Finset.range Q, ‖∑ j ∈ Finset.range m,
      Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (j:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))‖^2 : ℝ) : ℂ)
      = ((m:ℝ) * Q : ℝ) := by
    push_cast
    have step1 : ∀ y : ℕ, ((‖∑ j ∈ Finset.range m,
        Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (j:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))‖ : ℝ) : ℂ)^2
        = ∑ j ∈ Finset.range m, ∑ k ∈ Finset.range m,
            (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y := by
      intro y
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum,
        Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
      rw [← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_nat_mul]
      congr 1
      have hc : (starRingEnd ℂ) (2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (k:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ))
          = -(2*(Real.pi:ℂ)*Complex.I*(((x0:ℂ) + (k:ℂ)*(r:ℂ))*(y:ℂ))/(Q:ℂ)) := by
        simp [map_div₀, Complex.conj_I, map_ofNat]
        ring
      rw [hc]
      push_cast
      field_simp
      ring
    rw [Finset.sum_congr rfl (fun y (_ : y ∈ Finset.range Q) => step1 y), Finset.sum_comm]
    have step2 : ∀ j ∈ Finset.range m, (∑ k ∈ Finset.range m, ∑ y ∈ Finset.range Q,
        (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y)
        = (Q:ℂ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hinner : ∀ k ∈ Finset.range m, (∑ y ∈ Finset.range Q,
          (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y)
          = if j = k then (Q:ℂ) else 0 := by
        intro k hk
        rw [Finset.mem_range] at hk
        by_cases hjk : j = k
        · subst hjk; simp
        · rw [if_neg hjk]
          refine sum_exp_eq_zero Q (((j:ℤ) - k) * r) hQ ?_ (hspread j k hj hk hjk)
          exact mul_ne_zero (fun h0 => hjk (by omega)) hrZ
      rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq (Finset.range m) j (fun _ => (Q:ℂ))]
      simp [hj]
    have hfin : ∑ j ∈ Finset.range m, (∑ y ∈ Finset.range Q, ∑ k ∈ Finset.range m,
        (Complex.exp (2*(Real.pi:ℂ)*Complex.I*(((j:ℤ) - (k:ℤ))*(r:ℤ) : ℤ)/(Q:ℂ)))^y)
        = ∑ _j ∈ Finset.range m, (Q:ℂ) :=
      Finset.sum_congr rfl (fun j hj => by rw [Finset.sum_comm]; exact step2 j hj)
    rw [hfin]
    simp [mul_comm]
  exact_mod_cast hC

