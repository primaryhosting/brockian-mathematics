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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QI

open Finset Complex

/-!
## The Shor sampling distribution

We model the period-finding core of Shor's algorithm.  Fix a modulus `N`, a unit
`u : (ZMod N)ˣ` and a power-of-two-sized (any size, really) register `Q`.
The algorithm prepares

  `Q^{-1/2} ∑_{j < Q} |j⟩ |u ^ j⟩`,

applies the quantum Fourier transform modulo `Q` to the first register and
measures.  The probability of observing `c` in the first register and `y` in the
second one is `Q^{-2} ‖∑_{j < Q, u ^ j = y} e^{2πι c j / Q}‖^2`, so the marginal
probability of observing `c` is the following quantity.
-/

/-- Probability that Shor's period-finding circuit, run with modulus `N`, base `u`
and register size `Q`, outputs the value `c`. -/

lemma prob_lower {N : ℕ} [NeZero N] (u : (ZMod N)ˣ) {Q : ℕ} (hQ : (orderOf u) ^ 2 < Q)
    (c : ℕ) (s : ℤ) (hd : 2 * |(c : ℤ) * orderOf u - s * Q| ≤ orderOf u) :
    1 / (8 * (orderOf u : ℝ)) ≤ shorProb N u Q c := by
  set r := orderOf u with hrdef
  have hr : 0 < r := orderOf_pos u
  have hrr : r ≤ r ^ 2 := by nlinarith
  have hrQ : r ≤ Q := le_trans hrr hQ.le
  have hQ0 : 0 < Q := lt_of_lt_of_le hr hrQ
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  set d : ℤ := (c : ℤ) * r - s * Q with hddef
  set θ : ℝ := 2 * Real.pi * (d : ℝ) / Q with hθ
  have hexp : ∀ t : ℕ, Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)
      = Complex.exp ((θ * t : ℝ) * Complex.I) := by
    intro t
    have hc : (2 * (Real.pi : ℂ) * Complex.I * ((c : ℂ) * ((r : ℂ) * (t : ℂ))) / Q)
        = ((θ * t : ℝ) : ℂ) * Complex.I + ((s * t : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
      rw [hθ, hddef]
      push_cast
      field_simp
      ring
    rw [hc, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hkey : ∀ k ∈ range r, (4 / 25 : ℝ) * (blockCount Q r k : ℝ) ^ 2
      ≤ ‖∑ t ∈ range (blockCount Q r k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)‖ ^ 2 := by
    intro k _
    set A := blockCount Q r k with hA
    have hsimp : (∑ t ∈ range A, Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q))
        = ∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I) :=
      Finset.sum_congr rfl fun t _ => hexp t
    rw [hsimp]
    have hAR : (0 : ℝ) ≤ A := Nat.cast_nonneg A
    have hθA : θ ^ 2 * (A : ℝ) ^ 2 ≤ 14.4 :=
      theta_sq_bound hr hQ hQ0 (by rw [hddef]; exact hd) (blockCount_mul_le hr)
    have h1 : (2 / 5 : ℝ) * A ≤ (A : ℝ) * (1 - θ ^ 2 * ((A : ℝ) ^ 2 - 1) / 24) := by
      nlinarith [sq_nonneg θ, hθA, hAR]
    have h3 : (2 / 5 : ℝ) * A ≤ ‖∑ t ∈ range A, Complex.exp ((θ * t : ℝ) * Complex.I)‖ :=
      le_trans h1 (norm_sum_exp_lower θ A)
    nlinarith [h3, hAR]
  rw [shorProb_eq u hrQ c]
  have hsum : ∑ k ∈ range r, (blockCount Q r k : ℝ) = Q := by
    have h := sum_blockCount (Q := Q) (r := r) hr hrQ
    calc ∑ k ∈ range r, (blockCount Q r k : ℝ) = ((∑ k ∈ range r, blockCount Q r k : ℕ) : ℝ) := by
          push_cast; ring
      _ = Q := by rw [h]
  have hCS : (Q : ℝ) ^ 2 ≤ (r : ℝ) * ∑ k ∈ range r, (blockCount Q r k : ℝ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := range r) (f := fun k => (blockCount Q r k : ℝ))
    rw [Finset.card_range, hsum] at h
    exact h
  have hS : (Q : ℝ) ^ 2 / r ≤ ∑ k ∈ range r, (blockCount Q r k : ℝ) ^ 2 := by
    rw [div_le_iff₀ hrR]
    linarith [hCS]
  have hstep : (4 / 25 : ℝ) * ∑ k ∈ range r, (blockCount Q r k : ℝ) ^ 2
      ≤ ∑ k ∈ range r, ‖∑ t ∈ range (blockCount Q r k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hkey
  have hfinal : 1 / (8 * (r : ℝ)) ≤ (1 / (Q : ℝ) ^ 2) * ((4 / 25 : ℝ) * ((Q : ℝ) ^ 2 / r)) := by
    rw [show (1 / (Q : ℝ) ^ 2) * ((4 / 25 : ℝ) * ((Q : ℝ) ^ 2 / r)) = 4 / (25 * r) by field_simp]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  refine le_trans hfinal ?_
  have hlast : (4 / 25 : ℝ) * ((Q : ℝ) ^ 2 / r)
      ≤ ∑ k ∈ range r, ‖∑ t ∈ range (blockCount Q r k),
            Complex.exp (2 * Real.pi * Complex.I * (c * (r * t)) / Q)‖ ^ 2 := by
    refine le_trans ?_ hstep
    nlinarith [hS]
  exact mul_le_mul_of_nonneg_left hlast (by positivity)

/-! ### The classical post-processing -/

/-- An integer bound `2|cr - sQ| ≤ r` is exactly the statement that `s/r`
approximates `c/Q` to within `1/(2Q)`. -/
