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

noncomputable def upPoly (p : Polynomial ℝ) : Polynomial ℝ :=
  X * p - Polynomial.C (hbar / (2 * m * ω)) * derivative p

/-- Polynomial-level Hamiltonian (divided by `ℏω`): `H (p·gauss) = ℏω · (Mpoly p)·gauss`. -/
