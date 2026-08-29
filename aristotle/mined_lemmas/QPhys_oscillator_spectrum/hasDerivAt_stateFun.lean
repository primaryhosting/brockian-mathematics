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

lemma hasDerivAt_stateFun (p : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (stateFun m ω hbar p) (stateFun m ω hbar (Dpoly m ω hbar p) x) x := by
  have hp : HasDerivAt (fun y : ℝ => p.eval y) ((derivative p).eval x) x := p.hasDerivAt x
  have h := hp.mul (hasDerivAt_gauss m ω hbar x)
  convert h using 1
  simp [stateFun, Dpoly]
  ring

