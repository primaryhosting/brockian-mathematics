import Mathlib

/-!
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
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

/-- The Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-Ea / (R * T))

/-- For a positive pre-exponential factor `A`, positive activation energy `Ea`,
positive gas constant `R`, the Arrhenius rate `k(T) = A e^{-Ea/(RT)}` is strictly
increasing in the temperature `T` on the positive temperatures. -/
theorem arrhenius_monotone {A Ea R T₁ T₂ : ℝ} (hA : 0 < A) (hEa : 0 < Ea)
    (hR : 0 < R) (hT₁ : 0 < T₁) (hlt : T₁ < T₂) :
    arrhenius A Ea R T₁ < arrhenius A Ea R T₂ := by
  have hT₂ : 0 < T₂ := hT₁.trans hlt
  have h1 : 0 < R * T₁ := mul_pos hR hT₁
  have h2 : R * T₁ < R * T₂ := by nlinarith
  have hdiv : Ea / (R * T₂) < Ea / (R * T₁) := div_lt_div_of_pos_left hEa h1 h2
  have hexp : Real.exp (-Ea / (R * T₁)) < Real.exp (-Ea / (R * T₂)) := by
    apply Real.exp_lt_exp.mpr
    rw [neg_div, neg_div]
    linarith
  exact mul_lt_mul_of_pos_left hexp hA

/-- Packaged form: `T ↦ A e^{-Ea/(RT)}` is strictly monotone on `(0, ∞)`. -/
theorem strictMonoOn_arrhenius {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T : ℝ => arrhenius A Ea R T) (Set.Ioi 0) := by
  intro T₁ hT₁ T₂ _ hlt
  exact arrhenius_monotone hA hEa hR (Set.mem_Ioi.mp hT₁) hlt

end Chem

