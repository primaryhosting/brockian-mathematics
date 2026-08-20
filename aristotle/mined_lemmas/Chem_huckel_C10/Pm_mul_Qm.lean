import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

attribute [local instance] Fin.instCommRing

/-! ### A primitive 10-th root of unity -/

/-- The primitive 10-th root of unity `exp (2πi/10)`. -/

lemma Pm_mul_Qm : Pm * Qm = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have : ∀ k : Fin 10, Pm j k * Qm k l = (10 : ℂ)⁻¹ * E ((j - l) * k) := by
    intro k
    simp only [Pm, Qm]
    rw [← mul_assoc, mul_comm (E (j * k)) ((10:ℂ)⁻¹), mul_assoc, ← E_add]
    congr 2
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), ← Finset.mul_sum, E_sum]
  by_cases h : j = l
  · subst h
    simp
  · have : j - l ≠ 0 := sub_ne_zero_of_ne h
    simp [this, h]

