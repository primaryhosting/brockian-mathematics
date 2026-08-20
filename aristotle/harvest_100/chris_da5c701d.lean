import Mathlib

/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- **Van 't Hoff / Le Chatelier sign.**

Setting: `K : ℝ → ℝ` is the equilibrium constant as a function of the absolute
temperature `T > 0`, `R > 0` is the gas constant, and `dH` is the (constant)
standard reaction enthalpy.  The van 't Hoff equation says that

  `d/dT (log (K T)) = dH / (R * T ^ 2)`.

For an **exothermic** reaction (`dH < 0`) the equilibrium constant is strictly
decreasing in the temperature on `(0, ∞)`. -/
theorem leChatelier_sign
    (K : ℝ → ℝ) (R dH : ℝ) (hR : 0 < R) (hdH : dH < 0)
    (hKpos : ∀ T : ℝ, 0 < T → 0 < K T)
    (hvanthoff : ∀ T : ℝ, 0 < T →
      HasDerivAt (fun t : ℝ => Real.log (K t)) (dH / (R * T ^ 2)) T) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  -- First: `log ∘ K` is strictly decreasing on `(0, ∞)`.
  have hlog : StrictAntiOn (fun t : ℝ => Real.log (K t)) (Set.Ioi (0 : ℝ)) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0) ?_ ?_
    · intro T hT
      exact ((hvanthoff T hT).continuousAt).continuousWithinAt
    · intro T hT
      rw [interior_Ioi] at hT
      have hT' : 0 < T := hT
      rw [(hvanthoff T hT').deriv]
      have hden : 0 < R * T ^ 2 := by positivity
      exact div_neg_of_neg_of_pos hdH hden
  intro a ha b hb hab
  have hKa : 0 < K a := hKpos a ha
  have hKb : 0 < K b := hKpos b hb
  have h := hlog ha hb hab
  calc K b = Real.exp (Real.log (K b)) := (Real.exp_log hKb).symm
    _ < Real.exp (Real.log (K a)) := Real.exp_lt_exp.mpr h
    _ = K a := Real.exp_log hKa

end Chem

