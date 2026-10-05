/-
# Oscillator Spectrum
Category: Quantum Physics
Target: QPhys.oscillator_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

set_option autoImplicit false

namespace QPhys

open Polynomial

section Oscillator

variable (m ω hbar : ℝ)

/-- The Gaussian ground-state profile `exp (-m ω x² / (2ℏ))`. -/

noncomputable def Mpoly (p : Polynomial ℝ) : Polynomial ℝ :=
  -(Polynomial.C (hbar / (2 * m * ω)) * derivative (derivative p)) + X * derivative p
    + Polynomial.C (1 / 2) * p

/-- The eigenpolynomials, obtained by applying the raising operator `n` times to `1`. -/
