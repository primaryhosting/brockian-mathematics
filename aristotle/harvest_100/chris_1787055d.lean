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

/-- **Le Chatelier / van 't Hoff sign law.**

Let `K : ℝ → ℝ` be the equilibrium constant of a reaction as a function of the
absolute temperature `T > 0`.  Assume

* `K` takes positive values on `(0, ∞)`;
* `K` satisfies the van 't Hoff equation `d(log K)/dT = dH / (R T²)`, written in the
  equivalent derivative form `K'(T) = K T * dH / (R T²)`;
* the gas constant `R` is positive and the reaction enthalpy `dH` is negative
  (the reaction is *exothermic*).

Then `K` is strictly decreasing in `T` on `(0, ∞)`: heating an exothermic reaction
shifts the equilibrium towards the reactants. -/
theorem leChatelier_sign (R dH : ℝ) (hR : 0 < R) (hH : dH < 0) (K : ℝ → ℝ)
    (hKpos : ∀ T ∈ Set.Ioi (0 : ℝ), 0 < K T)
    (hvantHoff : ∀ T ∈ Set.Ioi (0 : ℝ), HasDerivAt K (K T * dH / (R * T ^ 2)) T) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  have hderiv : ∀ T ∈ Set.Ioi (0 : ℝ), deriv K T < 0 := by
    intro T hT
    have hT0 : (0 : ℝ) < T := hT
    have h := hvantHoff T hT
    rw [h.deriv]
    have hnum : K T * dH < 0 := mul_neg_of_pos_of_neg (hKpos T hT) hH
    have hden : 0 < R * T ^ 2 := mul_pos hR (by positivity)
    exact div_neg_of_neg_of_pos hnum hden
  have hcont : ContinuousOn K (Set.Ioi (0 : ℝ)) := fun T hT =>
    ((hvantHoff T hT).differentiableAt.continuousAt).continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) hcont ?_
  intro T hT
  rw [interior_Ioi] at hT
  exact hderiv T hT

end Chem

