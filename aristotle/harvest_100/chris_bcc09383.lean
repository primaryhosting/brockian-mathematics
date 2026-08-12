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
theorem leChatelier_sign
    (K : ℝ → ℝ) (R dH : ℝ) (hR : 0 < R) (hdH : dH < 0)
    (hpos : ∀ T : ℝ, 0 < T → 0 < K T)
    (hvantHoff : ∀ T : ℝ, 0 < T → HasDerivAt K (K T * (dH / (R * T ^ 2))) T) :
    StrictAntiOn K (Set.Ioi (0 : ℝ)) := by
  -- the derivative of `log ∘ K` is `dH / (R * T ^ 2)`, which is negative
  have hlog : ∀ T : ℝ, 0 < T → HasDerivAt (fun t => Real.log (K t)) (dH / (R * T ^ 2)) T := by
    intro T hT
    have hKT : K T ≠ 0 := ne_of_gt (hpos T hT)
    have h := (hvantHoff T hT).log hKT
    have heq : K T * (dH / (R * T ^ 2)) / K T = dH / (R * T ^ 2) := by
      rw [mul_comm, mul_div_assoc, div_self hKT, mul_one]
    rwa [heq] at h
  have hanti : StrictAntiOn (fun t => Real.log (K t)) (Set.Ioi (0 : ℝ)) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi (0 : ℝ))
    · intro T hT
      exact ((hlog T hT).differentiableAt).continuousAt.continuousWithinAt
    · intro T hT
      rw [interior_Ioi] at hT
      have hT' : 0 < T := hT
      rw [(hlog T hT').deriv]
      have : 0 < R * T ^ 2 := by positivity
      exact div_neg_of_neg_of_pos hdH this
  intro a ha b hb hab
  have h := hanti ha hb hab
  have hKa : 0 < K a := hpos a ha
  have hKb : 0 < K b := hpos b hb
  exact (Real.log_lt_log_iff hKb hKa).mp h

/-- Concrete instance: the integrated van 't Hoff law `K T = exp (C - dH / (R * T))`
with negative reaction enthalpy `dH` gives a strictly decreasing `K` on `(0, ∞)`. -/
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

