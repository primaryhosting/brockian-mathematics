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

noncomputable def lower (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (m * ω * x * f x + hbar * deriv f x) / Real.sqrt (2 * m * hbar * ω)

/-- Polynomial-level differentiation operator: if `f = p·gauss` then `f' = (Dpoly p)·gauss`. -/
