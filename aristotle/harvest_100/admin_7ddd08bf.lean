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

/-- The exponent `-Ea/(R*T)` is strictly increasing in `T > 0` when `Ea, R > 0`. -/
lemma arrhenius_exponent_lt {Ea R T₁ T₂ : ℝ} (hEa : 0 < Ea) (hR : 0 < R)
    (hT₁ : 0 < T₁) (hlt : T₁ < T₂) :
    -Ea / (R * T₁) < -Ea / (R * T₂) := by
  have h1 : 0 < R * T₁ := mul_pos hR hT₁
  rw [neg_div, neg_div, neg_lt_neg_iff]
  exact div_lt_div_of_pos_left hEa h1 (by nlinarith)

/-- **Arrhenius law is strictly increasing in temperature.**
For a positive pre-exponential factor `A`, positive activation energy `Ea` and positive
gas constant `R`, the rate `k(T) = A e^{-Ea/(R T)}` is strictly increasing on `T > 0`. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T => arrhenius A Ea R T) (Set.Ioi (0 : ℝ)) := by
  intro T₁ hT₁ T₂ _ hlt
  have := arrhenius_exponent_lt hEa hR (Set.mem_Ioi.mp hT₁) hlt
  simpa [arrhenius] using
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr this) hA

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

