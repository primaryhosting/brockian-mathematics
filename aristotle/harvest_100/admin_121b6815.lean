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
noncomputable def vantHoffK (R C ΔH T : ℝ) : ℝ := Real.exp (C - ΔH / (R * T))

/-- Van 't Hoff equation: `d/dT (log (K T)) = ΔH / (R T ^ 2)`. -/
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
theorem leChatelier_sign (R C ΔH : ℝ) (hR : 0 < R) (hH : ΔH < 0) :
    StrictAntiOn (vantHoffK R C ΔH) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hRa : 0 < R * a := by positivity
  have hRb : 0 < R * b := by positivity
  have hinv : (R * b)⁻¹ < (R * a)⁻¹ :=
    (inv_lt_inv₀ hRb hRa).mpr (by nlinarith)
  have key : ΔH * (R * a)⁻¹ < ΔH * (R * b)⁻¹ := mul_lt_mul_of_neg_left hinv hH
  have hlt : C - ΔH / (R * b) < C - ΔH / (R * a) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    linarith
  exact Real.exp_lt_exp.mpr hlt

end Chem

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

