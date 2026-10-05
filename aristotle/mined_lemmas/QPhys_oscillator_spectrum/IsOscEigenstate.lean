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

def IsOscEigenstate (hbar m omega E : ℝ) (f : ℝ → ℝ) : Prop :=
  f ≠ 0 ∧ ∃ f' f'' : ℝ → ℝ, (∀ x, HasDerivAt f (f' x) x) ∧ (∀ x, HasDerivAt f' (f'' x) x) ∧
    ∀ x, -(hbar ^ 2 / (2 * m)) * f'' x + (1 / 2) * m * omega ^ 2 * x ^ 2 * f x = E * f x

