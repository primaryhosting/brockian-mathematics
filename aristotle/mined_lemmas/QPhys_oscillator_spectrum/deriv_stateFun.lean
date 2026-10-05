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

lemma deriv_stateFun (p : Polynomial ℝ) :
    deriv (stateFun m ω hbar p) = stateFun m ω hbar (Dpoly m ω hbar p) := by
  funext x
  exact (hasDerivAt_stateFun m ω hbar p x).deriv

