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

noncomputable def eigenPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | (n + 1) => upPoly m ω hbar (eigenPoly n)

/-- The `n`-th eigenstate of the oscillator. -/
