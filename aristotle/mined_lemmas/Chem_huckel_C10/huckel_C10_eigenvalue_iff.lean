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

theorem huckel_C10_eigenvalue_iff (mu : ℂ) :
    (∃ v : Fin 10 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 10).adjMatrix ℂ *ᵥ v = mu • v) ↔
      ∃ k : ℕ, k < 10 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 10) : ℝ) : ℂ) := by
  have hsc : ∀ v : Fin 10 → ℂ, (Matrix.scalar (Fin 10) mu) *ᵥ v = mu • v := by
    intro v
    ext i
    simp [Matrix.scalar, Matrix.mulVec_diagonal]
  have key : (∃ v : Fin 10 → ℂ, v ≠ 0 ∧ (SimpleGraph.cycleGraph 10).adjMatrix ℂ *ᵥ v = mu • v) ↔
      (Matrix.scalar (Fin 10) mu - (SimpleGraph.cycleGraph 10).adjMatrix ℂ).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, h⟩
      exact ⟨v, hv, by rw [Matrix.sub_mulVec, h, hsc, sub_self]⟩
    · rintro ⟨v, hv, h⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hsc, sub_eq_zero] at h
      exact h.symm
  rw [key, ← Matrix.eval_charpoly, huckel_C10, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mp hk, sub_eq_zero.mp h⟩
  · rintro ⟨k, hk, h⟩
    exact ⟨k, Finset.mem_range.mpr hk, sub_eq_zero.mpr h⟩

end Chem

