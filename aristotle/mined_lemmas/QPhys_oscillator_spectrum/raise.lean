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

noncomputable def raise (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (m * ω * x * f x - hbar * deriv f x) / Real.sqrt (2 * m * hbar * ω)

/-- The annihilation (lowering) ladder operator `a = (mωx + ℏ d/dx)/√(2mℏω)`. -/
