import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

variable {N M : ℕ}

/-- A linear map between matrix algebras `M_N(ℂ) → M_M(ℂ)`. -/
abbrev MatMap (N M : ℕ) : Type :=
  Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin M) (Fin M) ℂ

/-- The amplification `id_{M_k} ⊗ Φ`, acting on `k × k` block matrices with blocks in
`M_N(ℂ)` by applying `Φ` to each block. -/

theorem transposeMap_not_isCompletelyPositive : ¬ IsCompletelyPositive transposeMap := by
  intro h
  have hpsd := (choi_jamiolkowski transposeMap).mp h
  set v : Fin 2 × Fin 2 → ℂ :=
    fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0 with hv
  have hval : star v ⬝ᵥ ((choiMatrix transposeMap) *ᵥ v) = -2 := by
    simp only [choiMatrix, transposeMap, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
      Fin.sum_univ_two, LinearEquiv.coe_coe, Matrix.transposeLinearEquiv_apply,
      Matrix.of_apply, Pi.star_apply, hv]
    norm_num
  have := hpsd.dotProduct_mulVec_nonneg v
  rw [hval, Complex.le_def] at this
  norm_num at this

end QI

