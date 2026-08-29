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

/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- **van 't Hoff sign lemma.**  If the equilibrium "constant" `K` is positive and
differentiable on the positive temperatures and satisfies the van 't Hoff equation
`d(log K)/dT = ΔH / (R T ^ 2)`, then for an exothermic reaction (`ΔH < 0`, with gas
constant `R > 0`) the derivative of `K` is strictly negative at every positive
temperature. -/

theorem leChatelier_sign
    (K : ℝ → ℝ) (R dH : ℝ) (hR : 0 < R) (hdH : dH < 0)
    (hKpos : ∀ T : ℝ, 0 < T → 0 < K T)
    (hKdiff : ∀ T : ℝ, 0 < T → DifferentiableAt ℝ K T)
    (hvantHoff : ∀ T : ℝ, 0 < T → deriv (fun t : ℝ => Real.log (K t)) T = dH / (R * T ^ 2)) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  have hcont : ContinuousOn K (Set.Ioi (0 : ℝ)) := fun T hT =>
    ((hKdiff T hT).continuousAt).continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ)) hcont ?_
  intro T hT
  rw [interior_Ioi] at hT
  exact deriv_neg_of_vantHoff K R dH hR hdH hKpos hKdiff hvantHoff T hT

end Chem

#print axioms Chem.leChatelier_sign

