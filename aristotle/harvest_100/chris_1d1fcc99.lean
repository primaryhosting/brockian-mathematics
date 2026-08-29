/-
# Le Chatelier Sign
Category: Chemistry
Target: Chem.leChatelier_sign
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Header kept verbatim; `/-!` had to become `/-` because Lean 4 forbids any command,
-- including a module docstring, before `import`.)

import Mathlib

namespace Chem

/-- **Van 't Hoff / Le Chatelier sign law.**

Let `K : ℝ → ℝ` be the equilibrium "constant" of a reaction as a function of the absolute
temperature `T > 0`, with `K T > 0`.  The van 't Hoff equation says that

  `d/dT (log (K T)) = ΔH / (R * T ^ 2)`,

where `R > 0` is the gas constant and `ΔH` the reaction enthalpy.  For an **exothermic**
reaction (`ΔH < 0`) the right-hand side is negative, so `K` is strictly decreasing on
`(0, ∞)`: raising the temperature shifts the equilibrium back towards the reactants.

The key Mathlib ingredients are `strictAntiOn_of_deriv_neg` and `Real.log_lt_log_iff`. -/
theorem leChatelier_sign (K : ℝ → ℝ) (R dH : ℝ) (hR : 0 < R) (hdH : dH < 0)
    (hKpos : ∀ T, 0 < T → 0 < K T)
    (hvantHoff : ∀ T, 0 < T → HasDerivAt (fun t => Real.log (K t)) (dH / (R * T ^ 2)) T) :
    StrictAntiOn K (Set.Ioi 0) := by
  have hlog : StrictAntiOn (fun t => Real.log (K t)) (Set.Ioi 0) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
      (fun x hx => (hvantHoff x hx).continuousAt.continuousWithinAt) ?_
    intro x hx
    rw [interior_Ioi] at hx
    have hx' : (0 : ℝ) < x := hx
    rw [(hvantHoff x hx').deriv]
    exact div_neg_of_neg_of_pos hdH (by positivity)
  intro x hx y hy hxy
  exact (Real.log_lt_log_iff (hKpos y hy) (hKpos x hx)).mp (hlog hx hy hxy)

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

