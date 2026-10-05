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

noncomputable def Dpoly (p : Polynomial ℝ) : Polynomial ℝ :=
  derivative p - Polynomial.C (m * ω / hbar) * (X * p)

/-- Polynomial-level raising operator: `a†(p·gauss) = const · (upPoly p)·gauss`. -/
