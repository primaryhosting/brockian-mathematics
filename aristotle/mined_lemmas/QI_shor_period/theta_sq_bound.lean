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

lemma theta_sq_bound {Q r A : ℕ} {d : ℤ} (hr : 0 < r) (hQ : r ^ 2 < Q) (hQ0 : 0 < Q)
    (hd : 2 * |d| ≤ (r : ℤ)) (hA : A * r + 1 ≤ Q + r) :
    (2 * Real.pi * (d : ℝ) / Q) ^ 2 * (A : ℝ) ^ 2 ≤ 14.4 := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hAR : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hQ' : r * r < Q := by nlinarith
  have h5 : 5 * r ≤ Q + 5 := by
    rcases Nat.lt_or_ge r 4 with h | h
    · interval_cases r <;> omega
    · nlinarith
  have h5R : 5 * (r : ℝ) ≤ (Q : ℝ) + 5 := by exact_mod_cast h5
  have hAR' : (A : ℝ) * r ≤ (Q : ℝ) + r - 1 := by
    have h : ((A * r + 1 : ℕ) : ℝ) ≤ ((Q + r : ℕ) : ℝ) := by exact_mod_cast hA
    push_cast at h
    linarith
  have hX : (A : ℝ) * r ≤ (6 / 5) * Q := by linarith
  have hdR : 4 * (d : ℝ) ^ 2 ≤ (r : ℝ) ^ 2 := by
    have h1 : |(d : ℝ)| * 2 ≤ (r : ℝ) := by
      have h : ((2 * |d| : ℤ) : ℝ) ≤ ((r : ℤ) : ℝ) := by exact_mod_cast hd
      push_cast at h
      linarith
    nlinarith [abs_nonneg (d : ℝ), sq_abs (d : ℝ)]
  have hpi : Real.pi ^ 2 ≤ 9.9225 := by nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have key : (2 * Real.pi * (d : ℝ) / Q) ^ 2 * (A : ℝ) ^ 2
      = Real.pi ^ 2 * (4 * (d : ℝ) ^ 2 * (A : ℝ) ^ 2) / (Q : ℝ) ^ 2 := by
    field_simp
    ring
  rw [key, div_le_iff₀ (by positivity)]
  have step2 : 4 * (d : ℝ) ^ 2 * (A : ℝ) ^ 2 ≤ ((r : ℝ) * A) ^ 2 := by nlinarith [sq_nonneg (A : ℝ)]
  have step3 : ((r : ℝ) * A) ^ 2 ≤ ((6 / 5) * Q) ^ 2 := by
    nlinarith [mul_nonneg (le_of_lt hrR) hAR]
  nlinarith [step2, step3, hpi, sq_nonneg ((Q : ℝ))]

/-- If `c / Q` is within `1 / (2Q)` of `s / r`, then `c` is observed with
probability at least `1 / (8 r)`. -/
