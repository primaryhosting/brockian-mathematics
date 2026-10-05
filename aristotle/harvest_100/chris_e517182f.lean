/-
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- **Van 't Hoff / Le Chatelier sign law.**

Let `K : ℝ → ℝ` be the equilibrium "constant" of a reaction as a function of the absolute
temperature `T > 0`.  Assume

* `K T > 0` for all `T > 0` (an equilibrium constant is positive),
* `K` is differentiable at each `T > 0`,
* the van 't Hoff equation holds: `d(log K)/dT = ΔH / (R * T ^ 2)`,
* the gas constant `R` is positive,
* the reaction is **exothermic**: `ΔH < 0`.

Then `K` is strictly decreasing on `(0, ∞)`: raising the temperature shifts an exothermic
equilibrium towards the reactants. -/
theorem leChatelier_sign (K : ℝ → ℝ) (ΔH R : ℝ)
    (hR : 0 < R) (hΔH : ΔH < 0)
    (hpos : ∀ T : ℝ, 0 < T → 0 < K T)
    (hdiff : ∀ T : ℝ, 0 < T → DifferentiableAt ℝ K T)
    (hvantHoff : ∀ T : ℝ, 0 < T →
      deriv (fun T => Real.log (K T)) T = ΔH / (R * T ^ 2)) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  -- First: `log ∘ K` is strictly antitone on `(0, ∞)`.
  have hlog : StrictAntiOn (fun T => Real.log (K T)) (Set.Ioi (0 : ℝ)) := by
    have hconv : Convex ℝ (Set.Ioi (0 : ℝ)) := convex_Ioi 0
    have hcont : ContinuousOn (fun T => Real.log (K T)) (Set.Ioi (0 : ℝ)) := by
      intro T hT
      have hT' : (0:ℝ) < T := hT
      exact ((Real.continuousAt_log (hpos T hT').ne').comp
        (hdiff T hT').continuousAt).continuousWithinAt
    apply strictAntiOn_of_deriv_neg hconv hcont
    intro T hT
    rw [interior_Ioi] at hT
    have hT' : (0:ℝ) < T := hT
    rw [hvantHoff T hT']
    exact div_neg_of_neg_of_pos hΔH (by positivity)
  intro a ha b hb hab
  have h := hlog ha hb hab
  simpa using (Real.log_lt_log_iff (hpos b hb) (hpos a ha)).mp h

end Chem

-- Axiom check: depends only on `propext`, `Classical.choice`, `Quot.sound`.
#print axioms Chem.leChatelier_sign

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

