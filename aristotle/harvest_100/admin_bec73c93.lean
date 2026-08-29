/- Requested header (Lean 4 requires `import` lines to precede any module docstring,
   so the header is reproduced verbatim here as a plain comment and again below):
/-!
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
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

/-- For a positive pre-exponential factor `A`, positive gas constant `R`, and positive
activation energy `Ea`, the Arrhenius rate `k(T) = A e^{-Ea/(R T)}` is strictly increasing
in the temperature `T` on the positive reals. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (arrhenius A Ea R) (Set.Ioi (0 : ℝ)) := by
  intro T₁ hT₁ T₂ _ hlt
  have hT₁ : (0 : ℝ) < T₁ := hT₁
  have hT₂ : (0 : ℝ) < T₂ := hT₁.trans hlt
  have hb : 0 < R * T₁ := by positivity
  have hbc : R * T₁ < R * T₂ := mul_lt_mul_of_pos_left hlt hR
  have hc : 0 < R * T₂ := hb.trans hbc
  have hinv : (R * T₂)⁻¹ < (R * T₁)⁻¹ := by
    rw [inv_lt_inv₀ hc hb]; exact hbc
  have hdiv : -Ea / (R * T₁) < -Ea / (R * T₂) := by
    simpa [div_eq_mul_inv] using mul_lt_mul_of_neg_left hinv (by linarith : -Ea < 0)
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 hdiv) hA

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

