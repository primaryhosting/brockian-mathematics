/-
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- The van 't Hoff equilibrium constant: `ln K(T) = C - ΔH / (R T)`, i.e.
`K(T) = exp (C - ΔH / (R * T))`, where `ΔH` is the reaction enthalpy, `R > 0` the
gas constant and `C` an integration constant. -/

theorem deriv_log_vantHoffK (R C ΔH T : ℝ) (hR : 0 < R) (hT : 0 < T) :
    HasDerivAt (fun T => Real.log (vantHoffK R C ΔH T)) (ΔH / (R * T ^ 2)) T := by
  have hRT : R * T ≠ 0 := by positivity
  have h1 : (fun T => Real.log (vantHoffK R C ΔH T)) = fun s => C - ΔH * (R * s)⁻¹ := by
    funext s; simp [vantHoffK, div_eq_mul_inv]
  have hd : HasDerivAt (fun s : ℝ => R * s) R T := by
    simpa using (hasDerivAt_id T).const_mul R
  have h2 : HasDerivAt (fun s : ℝ => (R * s)⁻¹) (-R / (R * T) ^ 2) T := hd.inv hRT
  have h3 := (hasDerivAt_const T C).sub (h2.const_mul ΔH)
  rw [h1]
  convert h3 using 1
  field_simp
  ring

/-- **Le Chatelier sign / van 't Hoff.** For an exothermic reaction (`ΔH < 0`), the
equilibrium constant `K(T) = exp (C - ΔH / (R T))` is strictly decreasing in the
temperature `T > 0`. -/
