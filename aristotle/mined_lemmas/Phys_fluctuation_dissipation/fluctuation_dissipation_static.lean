import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
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

namespace Phys

/-- Derivative of an exponentially decaying observable `t ↦ c e^{-a t}`. -/

theorem fluctuation_dissipation_static (S : LangevinSystem) :
    (∫ t in Set.Ioi (0 : ℝ), S.response t) = S.beta * S.corr 0 := by
  have hrate := S.relaxRate_pos
  have hint : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(S.relaxRate * t)))
      = 1 / S.relaxRate := by
    have := integral_exp_mul_Ioi (a := -S.relaxRate) (by linarith) 0
    simp only [neg_mul, mul_zero, Real.exp_zero] at this
    rw [this]
    field_simp
  have hk := S.k_pos.ne'
  have hb := S.beta_pos.ne'
  have hg := S.gamma_pos.ne'
  simp only [response, corr_zero]
  rw [MeasureTheory.integral_const_mul, hint]
  simp only [LangevinSystem.relaxRate]
  field_simp

end Phys

