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

lemma hasDerivAt_psi (n : ℕ) (y : ℝ) :
    HasDerivAt (psi n) ((Dop (Hr n)).eval y * Real.exp (-(y ^ 2 / 4))) y :=
  hasDerivAt_polyGauss (Hr n) y

