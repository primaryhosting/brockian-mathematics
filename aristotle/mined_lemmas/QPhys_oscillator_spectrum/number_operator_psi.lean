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

lemma number_operator_psi (n : ℕ) :
    creation (annihilation (psi n)) = fun y => (n : ℝ) * psi n y := by
  cases n with
  | zero =>
      rw [annihilation_psi_zero]
      funext y
      simp [creation]
  | succ n =>
      rw [annihilation_psi_succ n]
      funext y
      have hderiv : deriv (fun y => ((n : ℝ) + 1) * psi n y) y = ((n : ℝ) + 1) * deriv (psi n) y :=
        deriv_const_mul _ (hasDerivAt_psi n y).differentiableAt
      have := congrFun (creation_psi n) y
      simp only [creation, hderiv] at this ⊢
      push_cast
      nlinarith [this]

/-- The key polynomial identity behind the eigenvalue equation. -/
