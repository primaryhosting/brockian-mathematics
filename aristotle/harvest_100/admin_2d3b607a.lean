/-
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
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

/-- **Le Chatelier sign / van 't Hoff.**

Let `K : ℝ → ℝ` be the equilibrium "constant" of a reaction as a function of the absolute
temperature `T > 0`.  Assume:

* the gas constant `R` is positive;
* the reaction is *exothermic*, i.e. its enthalpy change satisfies `ΔH < 0`;
* `K T > 0` for every `T > 0`;
* the van 't Hoff equation holds: `d/dT (log (K T)) = ΔH / (R * T ^ 2)` for `T > 0`.

Then `K` is strictly decreasing on `(0, ∞)`: raising the temperature shifts an exothermic
equilibrium towards the reactants. -/
theorem leChatelier_sign {K : ℝ → ℝ} {ΔH R : ℝ}
    (hR : 0 < R) (hΔH : ΔH < 0)
    (hKpos : ∀ T : ℝ, 0 < T → 0 < K T)
    (hvantHoff : ∀ T : ℝ, 0 < T →
      HasDerivAt (fun S : ℝ => Real.log (K S)) (ΔH / (R * T ^ 2)) T) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  have hlog : StrictAntiOn (fun S : ℝ => Real.log (K S)) (Set.Ioi (0 : ℝ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
    · intro T hT
      exact ((hvantHoff T hT).continuousAt).continuousWithinAt
    · intro T hT
      rw [interior_Ioi] at hT
      have hT' : (0 : ℝ) < T := hT
      rw [(hvantHoff T hT').deriv]
      have hden : 0 < R * T ^ 2 := by positivity
      exact div_neg_of_neg_of_pos hΔH hden
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have := hlog hx hy hxy
  exact (Real.log_lt_log_iff (hKpos y hy') (hKpos x hx')).mp this

/-- Concrete van 't Hoff / Arrhenius form: `K T = A * exp (-ΔH / (R * T))` with `A > 0`,
`R > 0` and `ΔH < 0` (exothermic) is strictly decreasing in `T` on `(0, ∞)`. -/
theorem leChatelier_sign_exp {A ΔH R : ℝ} (hA : 0 < A) (hR : 0 < R) (hΔH : ΔH < 0) :
    StrictAntiOn (fun T : ℝ => A * Real.exp (-ΔH / (R * T))) (Set.Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  have hlt : -ΔH / (R * y) < -ΔH / (R * x) := by
    have h1 : 0 < R * x := by positivity
    have h2 : 0 < R * y := by positivity
    rw [div_lt_div_iff₀ h2 h1]
    nlinarith [mul_pos (mul_pos (neg_pos.mpr hΔH) hR) (sub_pos.mpr hxy)]
  have := Real.exp_lt_exp.mpr hlt
  simpa using (mul_lt_mul_of_pos_left this hA)

end Chem

