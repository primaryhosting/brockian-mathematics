import Mathlib

/-!
# Integral Sinc Fourth
Category: C Integral
Target: Zeta23Scaffold.integral_sinc_fourth
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Zeta23Scaffold

open MeasureTheory Real FourierTransform intervalIntegral

/-! ## The tent function and its Fourier transform -/

/-- The tent (triangle) function, supported on `[-1, 1]`. -/

lemma hasCompactSupport_tentC : HasCompactSupport tentC := by
  apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  intro x hx
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  have h : 1 ≤ |x| := by
    rcases hx with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  simp [tentC, tent_eq_zero h]

