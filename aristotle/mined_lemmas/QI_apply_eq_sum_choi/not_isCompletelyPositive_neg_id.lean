import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ` between matrix algebras:
`C(Φ) (i, α) (j, β) = Φ (Eᵢⱼ) α β`, where `Eᵢⱼ` is the matrix unit. -/

theorem not_isCompletelyPositive_neg_id :
    ¬ IsCompletelyPositive (-LinearMap.id : Matrix (Fin 1) (Fin 1) ℂ →ₗ[ℂ]
      Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [choi_jamiolkowski]
  intro h
  have h1 := h.diag_nonneg (i := (0, 0))
  simp only [choi, Matrix.of_apply, LinearMap.neg_apply, LinearMap.id_apply, Matrix.neg_apply,
    Matrix.single_apply, and_self, if_true, Left.nonneg_neg_iff] at h1
  exact absurd h1 (by norm_num)

end QI

