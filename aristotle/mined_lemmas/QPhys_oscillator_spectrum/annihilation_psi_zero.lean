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

lemma annihilation_psi_zero : annihilation (psi 0) = 0 := by
  funext y
  simp only [annihilation, psi, deriv_psi 0, Dop, Hr_zero]
  simp only [derivative_one, eval_sub, eval_mul, eval_C, eval_X, eval_one, zero_sub]
  simp
  ring

/-- The number operator `N = a† a` has eigenvalue `n` on `ψₙ`. -/
