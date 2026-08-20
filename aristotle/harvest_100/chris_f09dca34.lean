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
-- (Lean 4 requires `import` lines to precede every other command, including
-- module doc comments, so the requested header appears immediately below.)
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

/-- For a positive pre-exponential factor `A`, positive activation energy `Ea`, and
positive gas constant `R`, the Arrhenius rate `k = A e^{-Ea/(R T)}` is strictly
increasing in the (positive) temperature `T`. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T : ℝ => arrhenius A Ea R T) (Set.Ioi 0) := by
  intro T₁ h₁ T₂ h₂ h12
  simp only [Set.mem_Ioi] at h₁ h₂
  have hRT₁ : 0 < R * T₁ := mul_pos hR h₁
  have hRT₂ : 0 < R * T₂ := mul_pos hR h₂
  have hlt : -Ea / (R * T₁) < -Ea / (R * T₂) := by
    rw [div_lt_div_iff₀ hRT₁ hRT₂]
    nlinarith [mul_pos (mul_pos hEa hR) (sub_pos.2 h12)]
  simpa [arrhenius] using mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 hlt) hA

end Chem

