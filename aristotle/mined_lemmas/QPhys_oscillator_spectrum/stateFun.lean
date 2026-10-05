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

noncomputable def stateFun (p : Polynomial ℝ) : ℝ → ℝ :=
  fun x => p.eval x * gauss m ω hbar x

/-- The harmonic-oscillator Hamiltonian `H = -ℏ²/(2m) d²/dx² + ½ m ω² x²`. -/
