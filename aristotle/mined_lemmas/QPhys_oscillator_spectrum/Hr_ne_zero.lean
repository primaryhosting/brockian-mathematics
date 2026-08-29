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

lemma Hr_ne_zero (n : ℕ) : Hr n ≠ 0 :=
  ((Polynomial.hermite_monic n).map (Int.castRingHom ℝ)).ne_zero

/-! ## The dimensionless oscillator -/

/-- The polynomial part of `(y/2 - d/dy)` acting on `p(y) e^{-y²/4}` (up to sign):
if `f(y) = p(y) e^{-y²/4}` then `f'(y) = (Dop p)(y) e^{-y²/4}`. -/
