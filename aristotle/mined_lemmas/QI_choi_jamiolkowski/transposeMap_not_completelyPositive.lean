/-
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
# Choi–Jamiołkowski

This file develops, for linear maps `Φ : Mₘ(ℂ) →ₗ[ℂ] Mₙ(ℂ)`, the equivalence between

* complete positivity of `Φ` (every ampliation `Φ ⊗ id_k` preserves positive semidefiniteness),
* positive semidefiniteness of the Choi matrix `C(Φ)`,
* existence of a Kraus (operator sum) representation of `Φ`.
-/

namespace QI

open Matrix

variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The Choi matrix of a linear map `Φ : Mₘ(ℂ) →ₗ[ℂ] Mₙ(ℂ)`, given by
`C_{(i,a),(j,b)} = (Φ Eᵢⱼ)_{a b}` where `Eᵢⱼ` are the matrix units. -/

theorem transposeMap_not_completelyPositive : ¬ IsCompletelyPositive transposeMap := by
  rw [choi_jamiolkowski]
  intro h
  have hd := h.dotProduct_mulVec_nonneg
    (fun p : Fin 2 × Fin 2 => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0)
  simp [choiMatrix, transposeMap, Matrix.mulVec, dotProduct, Matrix.single_apply,
    Fintype.sum_prod_type, Fin.sum_univ_succ] at hd
  norm_num at hd

end Example

end QI

