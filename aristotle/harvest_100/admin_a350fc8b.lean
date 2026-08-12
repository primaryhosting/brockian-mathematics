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

/-- The Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))`,
with pre-exponential factor `A`, activation energy `Ea`, gas constant `R`
and absolute temperature `T`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-Ea / (R * T))

/-- For a positive activation energy `Ea`, positive pre-exponential factor `A` and
positive gas constant `R`, the Arrhenius rate `k(T) = A e^{-Ea/(R T)}` is strictly
increasing in the absolute temperature `T > 0`. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T : ℝ => arrhenius A Ea R T) (Set.Ioi (0 : ℝ)) := by
  intro T₁ hT₁ T₂ hT₂ hlt
  have hT₁0 : (0 : ℝ) < T₁ := hT₁
  have hT₂0 : (0 : ℝ) < T₂ := hT₂
  have h1 : (0 : ℝ) < R * T₁ := mul_pos hR hT₁0
  have h2 : (0 : ℝ) < R * T₂ := mul_pos hR hT₂0
  have hexp : -Ea / (R * T₁) < -Ea / (R * T₂) := by
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith [mul_lt_mul_of_pos_left hlt (mul_pos hEa hR)]
  have := Real.exp_lt_exp.2 hexp
  simpa [arrhenius] using (mul_lt_mul_of_pos_left this hA)

end Chem

