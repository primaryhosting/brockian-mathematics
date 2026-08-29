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

noncomputable def gauss (x : ℝ) : ℝ := Real.exp (-(m * ω / (2 * hbar)) * x ^ 2)

/-- A state of the form (polynomial) × (Gaussian). -/
