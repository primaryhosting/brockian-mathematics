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

/-- For a positive prefactor `A`, positive activation energy `Ea` and positive gas
constant `R`, the Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))` is
strictly increasing in the temperature `T` (on positive temperatures). -/
theorem arrhenius_monotone {A Ea R T₁ T₂ : ℝ} (hA : 0 < A) (hEa : 0 < Ea)
    (hR : 0 < R) (hT₁ : 0 < T₁) (hT : T₁ < T₂) :
    arrhenius A Ea R T₁ < arrhenius A Ea R T₂ := by
  have hRT₁ : 0 < R * T₁ := mul_pos hR hT₁
  have hlt : R * T₁ < R * T₂ := by nlinarith
  have hkey : Ea / (R * T₂) < Ea / (R * T₁) :=
    div_lt_div_of_pos_left hEa hRT₁ hlt
  have hexp : -Ea / (R * T₁) < -Ea / (R * T₂) := by
    rw [neg_div, neg_div]
    linarith
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) hA

end Chem

