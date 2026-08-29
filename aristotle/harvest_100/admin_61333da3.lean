import Mathlib
/-!
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note: Lean 4 requires `import` statements to precede every other command, including
module doc comments, so the required header comment is placed directly after the
single `import Mathlib` line.
-/

namespace Chem

/-- **Van 't Hoff / Le Chatelier sign law.**

Let `K : ℝ → ℝ` be the equilibrium "constant" of a reaction as a function of the absolute
temperature `T > 0`, with gas constant `R > 0` and reaction enthalpy `dH`.  Assume `K` is
positive and differentiable on `(0, ∞)` and satisfies the van 't Hoff equation

  `K'(T) = K(T) * dH / (R * T ^ 2)`   (equivalently `d/dT log K = dH / (R T²)`).

If the reaction is exothermic, i.e. `dH < 0`, then `K` is strictly decreasing on `(0, ∞)`:
raising the temperature shifts the equilibrium away from the products. -/
theorem leChatelier_sign (R dH : ℝ) (hR : 0 < R) (hH : dH < 0) (K : ℝ → ℝ)
    (hKpos : ∀ T, 0 < T → 0 < K T)
    (hKdiff : ∀ T, 0 < T → DifferentiableAt ℝ K T)
    (hvanTHoff : ∀ T, 0 < T → deriv K T = K T * dH / (R * T ^ 2)) :
    StrictAntiOn K (Set.Ioi 0) := by
  have hcont : ContinuousOn K (Set.Ioi 0) := fun T hT =>
    ((hKdiff T hT).continuousAt).continuousWithinAt
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) hcont ?_
  intro T hT
  rw [interior_Ioi] at hT
  have hT0 : (0 : ℝ) < T := hT
  rw [hvanTHoff T hT0]
  have hden : 0 < R * T ^ 2 := by positivity
  have hnum : K T * dH < 0 := mul_neg_of_pos_of_neg (hKpos T hT0) hH
  exact div_neg_of_neg_of_pos hnum hden

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

