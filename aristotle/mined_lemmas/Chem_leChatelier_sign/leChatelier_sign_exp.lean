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

/-- **Le Chatelier / van 't Hoff sign law.**

Let `K : ℝ → ℝ` be the equilibrium "constant" of a reaction as a function of the absolute
temperature `T > 0`.  Assume

* `R > 0` is the gas constant,
* the reaction enthalpy `dH` is negative (the reaction is *exothermic*),
* `K` is positive at every positive temperature,
* `K` satisfies the van 't Hoff equation `d K / d T = K * dH / (R * T ^ 2)`
  (equivalently `d (log K) / d T = dH / (R * T ^ 2)`).

Then `K` is strictly decreasing on `(0, ∞)`: heating an exothermic reaction shifts the
equilibrium back towards the reactants. -/

theorem leChatelier_sign_exp (R dH C : ℝ) (hR : 0 < R) (hdH : dH < 0) :
    StrictAntiOn (fun T : ℝ => Real.exp (C - dH / (R * T))) (Set.Ioi (0 : ℝ)) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  refine Real.exp_lt_exp.mpr ?_
  have h1 : 0 < R * a := by positivity
  have h2 : 0 < R * b := by positivity
  have hsub : dH / (R * a) - dH / (R * b) < 0 := by
    have hrw : dH / (R * a) - dH / (R * b) = dH * (R * b - R * a) / ((R * a) * (R * b)) := by
      field_simp
    rw [hrw]
    have hd : 0 < R * b - R * a := by nlinarith
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdH hd) (by positivity)
  linarith

end Chem

#print axioms Chem.leChatelier_sign
#print axioms Chem.leChatelier_sign_exp

