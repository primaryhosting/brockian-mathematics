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

noncomputable def eigenState (n : ℕ) : ℝ → ℝ := stateFun m ω hbar (eigenPoly m ω hbar n)

end Oscillator

end QPhys

namespace QPhys
open Polynomial
section Oscillator
variable (m ω hbar : ℝ)

