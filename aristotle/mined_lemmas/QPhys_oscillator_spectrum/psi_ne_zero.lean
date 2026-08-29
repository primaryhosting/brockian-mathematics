/-!
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Polynomial

namespace QPhys

/-! ## Hermite polynomials over `ℝ`

We reuse Mathlib's (probabilists') Hermite polynomials `Polynomial.hermite : ℕ → ℤ[X]`
(`Mathlib/RingTheory/Polynomial/Hermite/Basic.lean`), pushed forward to `ℝ[X]`.
-/

/-- The `n`-th (probabilists') Hermite polynomial, with real coefficients. -/

lemma psi_ne_zero (n : ℕ) : ∃ y : ℝ, psi n y ≠ 0 := by
  by_contra h
  push_neg at h
  refine Hr_ne_zero n (Polynomial.funext fun y => ?_)
  have := h y
  simp only [psi, mul_eq_zero] at this
  rcases this with h1 | h2
  · simpa using h1
  · exact absurd h2 (Real.exp_ne_zero _)

/-! ## The physical oscillator -/

/-- The characteristic inverse length `c = √(2mω/ℏ)`. -/
