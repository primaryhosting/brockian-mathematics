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

lemma hasDerivAt_gauss (x : ℝ) :
    HasDerivAt (gauss m ω hbar) (-(m * ω / hbar) * x * gauss m ω hbar x) x := by
  have h1 : HasDerivAt (fun y : ℝ => -(m * ω / (2 * hbar)) * y ^ 2)
      (-(m * ω / (2 * hbar)) * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul (-(m * ω / (2 * hbar)))
  have h2 := (Real.hasDerivAt_exp (-(m * ω / (2 * hbar)) * x ^ 2)).comp x h1
  have hd : m * ω / (2 * hbar) = (m * ω / hbar) / 2 := by
    rw [show (2 : ℝ) * hbar = hbar * 2 from mul_comm _ _, ← div_div]
  convert h2 using 1
  unfold gauss
  rw [hd]
  ring

