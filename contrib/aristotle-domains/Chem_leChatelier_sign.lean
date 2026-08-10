/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Statement: For an exothermic reaction, the equilibrium constant K(T) is strictly decreasing in T (van 't Hoff).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Chem

/-- **Van 't Hoff / Le Chatelier sign law.**

If the equilibrium "constant" `K : ℝ → ℝ` is a positive function of the absolute
temperature `T > 0` satisfying the van 't Hoff equation
`K'(T) = (ΔH / (R T²)) · K(T)`  (equivalently `d(log K)/dT = ΔH / (R T²)`)
with gas constant `R > 0`, then for an *exothermic* reaction (`ΔH < 0`) the map
`T ↦ K T` is strictly decreasing on `(0, ∞)`. -/
theorem leChatelier_sign (R dH : ℝ) (K : ℝ → ℝ) (hR : 0 < R) (hH : dH < 0)
    (hKpos : ∀ T ∈ Set.Ioi (0 : ℝ), 0 < K T)
    (hvantHoff : ∀ T ∈ Set.Ioi (0 : ℝ), HasDerivAt K (dH / (R * T ^ 2) * K T) T) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn K (Set.Ioi (0 : ℝ)) := fun T hT =>
    ((hvantHoff T hT).continuousAt).continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) hcont ?_
  intro T hT
  rw [interior_Ioi] at hT
  have hT0 : (0 : ℝ) < T := hT
  rw [(hvantHoff T hT).deriv]
  have hden : 0 < R * T ^ 2 := by positivity
  have h1 : dH / (R * T ^ 2) < 0 := div_neg_of_neg_of_pos hH hden
  exact mul_neg_of_neg_of_pos h1 (hKpos T hT)

/-- Closed-form instance of the previous theorem: with `K T = A * exp (- dH / (R * T))`
(the integrated van 't Hoff equation), an exothermic reaction (`dH < 0`) has a
strictly decreasing equilibrium constant on `(0, ∞)`. -/
theorem leChatelier_sign_explicit (R dH A : ℝ) (hR : 0 < R) (hH : dH < 0) (hA : 0 < A) :
    StrictAntiOn (fun T : ℝ => A * Real.exp (-dH / (R * T))) (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) < x := hx
  have hy0 : (0 : ℝ) < y := hy
  have key : -dH / (R * y) < -dH / (R * x) := by
    have hxr : 0 < R * x := by positivity
    have hyr : 0 < R * y := by positivity
    rw [div_lt_div_iff₀ hyr hxr]
    have hd : (0 : ℝ) < -dH := by linarith
    nlinarith [mul_pos hd (mul_pos hR (sub_pos.mpr hxy))]
  have := Real.exp_lt_exp.mpr key
  simpa using (mul_lt_mul_of_pos_left this hA)

end Chem

#print axioms Chem.leChatelier_sign
#print axioms Chem.leChatelier_sign_explicit

