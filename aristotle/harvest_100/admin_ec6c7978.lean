import Mathlib
/-!
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- The Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-Ea / (R * T))

/-- For a positive pre-exponential factor `A`, positive activation energy `Ea`
and positive gas constant `R`, the Arrhenius rate constant is strictly increasing
in the temperature `T` on the positive temperatures. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T => arrhenius A Ea R T) (Set.Ioi (0 : ℝ)) := by
  intro T₁ hT₁ T₂ hT₂ h
  simp only [Set.mem_Ioi] at hT₁ hT₂
  have key : Ea / (R * T₂) < Ea / (R * T₁) :=
    div_lt_div_of_pos_left hEa (by positivity) (by nlinarith)
  have hexp : -Ea / (R * T₁) < -Ea / (R * T₂) := by
    rw [neg_div, neg_div]
    linarith
  simpa [arrhenius] using mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 hexp) hA

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

