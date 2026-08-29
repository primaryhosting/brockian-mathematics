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

noncomputable def scale (hbar m omega : ℝ) : ℝ := Real.sqrt (2 * m * omega / hbar)

/-- The `n`-th (unnormalised) energy eigenfunction of the harmonic oscillator
`H = -(ℏ²/2m) d²/dx² + (1/2) m ω² x²`, obtained from the ground state by the ladder operators. -/
