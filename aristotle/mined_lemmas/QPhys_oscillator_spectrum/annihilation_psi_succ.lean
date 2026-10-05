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

lemma annihilation_psi_succ (n : ℕ) :
    annihilation (psi (n + 1)) = fun y => ((n : ℝ) + 1) * psi n y := by
  funext y
  simp only [annihilation, psi, deriv_psi (n + 1), Dop, Hr_deriv_succ n]
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_natCast]
  ring

/-- `a ψ₀ = 0`: the ground state is annihilated by the lowering operator. -/
