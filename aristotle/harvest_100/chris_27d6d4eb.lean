import Mathlib
/-!
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The Arrhenius rate constant `k(T) = A · exp (-Ea / (R * T))`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-(Ea / (R * T)))

/-- For a positive pre-exponential factor `A`, positive activation energy `Ea` and
positive gas constant `R`, the Arrhenius rate `k(T) = A exp (-Ea/(R T))` is strictly
increasing in the (positive) temperature `T`.

The key Mathlib ingredients are `Real.exp_lt_exp` (strict monotonicity of `exp`) and
`div_lt_div_of_pos_left` (antitonicity of `Ea / x` in `x` for `Ea > 0`). -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T₂) :
    arrhenius A Ea R T₁ < arrhenius A Ea R T₂ := by
  have hT₂ : 0 < T₂ := hT₁.trans hT
  unfold arrhenius
  have hexp : Real.exp (-(Ea / (R * T₁))) < Real.exp (-(Ea / (R * T₂))) := by
    apply Real.exp_lt_exp.mpr
    have h1 : 0 < R * T₁ := mul_pos hR hT₁
    have : Ea / (R * T₂) < Ea / (R * T₁) :=
      div_lt_div_of_pos_left hEa h1 (by nlinarith)
    linarith
  exact mul_lt_mul_of_pos_left hexp hA

/-- Restated as strict monotonicity on the set of positive temperatures. -/
theorem arrhenius_strictMonoOn {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (arrhenius A Ea R) (Set.Ioi 0) := fun _ hx _ _ hxy =>
  arrhenius_monotone hA hEa hR hx hxy

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

