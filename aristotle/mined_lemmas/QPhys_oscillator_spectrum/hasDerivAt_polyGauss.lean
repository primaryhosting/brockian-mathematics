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

lemma hasDerivAt_polyGauss (p : Polynomial ℝ) (y : ℝ) :
    HasDerivAt (fun t : ℝ => p.eval t * Real.exp (-(t ^ 2 / 4)))
      ((Dop p).eval y * Real.exp (-(y ^ 2 / 4))) y := by
  have h1 : HasDerivAt (fun t : ℝ => p.eval t) ((derivative p).eval y) y := p.hasDerivAt y
  have h2 : HasDerivAt (fun t : ℝ => -(t ^ 2 / 4)) (-(y / 2)) y := by
    have : HasDerivAt (fun t : ℝ => t ^ 2 / 4) (y / 2) y := by
      have := (hasDerivAt_pow 2 y).div_const 4
      simpa using this.congr_deriv (by ring)
    simpa using this.neg
  refine (h1.mul h2.exp).congr_deriv ?_
  simp [Dop]
  ring

