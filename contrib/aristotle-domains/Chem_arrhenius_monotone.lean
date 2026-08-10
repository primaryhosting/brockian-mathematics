/-!
# Arrhenius Monotone
Category: Chemistry
Target: Chem.arrhenius_monotone
Statement: The Arrhenius rate k=A e^{−Ea/RT} is strictly increasing in T for Ea>0.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The Arrhenius rate constant `k(T) = A * exp (-Ea / (R * T))`. -/
noncomputable def arrhenius (A Ea R T : ℝ) : ℝ := A * Real.exp (-Ea / (R * T))

/-- For a positive pre-exponential factor `A`, positive activation energy `Ea` and
positive gas constant `R`, the Arrhenius rate `k(T) = A e^{-Ea/(R T)}` is strictly
increasing in the temperature `T` on the positive reals. -/
theorem arrhenius_monotone {A Ea R : ℝ} (hA : 0 < A) (hEa : 0 < Ea) (hR : 0 < R) :
    StrictMonoOn (fun T : ℝ => arrhenius A Ea R T) (Set.Ioi 0) := by
  intro T₁ hT₁ T₂ hT₂ h
  have hT₁' : (0 : ℝ) < T₁ := hT₁
  have hT₂' : (0 : ℝ) < T₂ := hT₂
  have h1 : 0 < R * T₁ := mul_pos hR hT₁'
  have h2 : 0 < R * T₂ := mul_pos hR hT₂'
  have hlt : -Ea / (R * T₁) < -Ea / (R * T₂) := by
    rw [neg_div, neg_div, neg_lt_neg_iff, div_lt_div_iff_of_pos_left hEa h2 h1]
    exact mul_lt_mul_of_pos_left h hR
  simp only [arrhenius]
  exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 hlt) hA

end Chem

