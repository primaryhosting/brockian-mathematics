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

lemma creation_psi (n : ℕ) : creation (psi n) = psi (n + 1) := by
  funext y
  simp only [creation, psi, deriv_psi n, Dop, Hr_succ n]
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  ring

/-- `a` lowers: `a ψₙ₊₁ = (n+1) ψₙ`. -/
