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

lemma kraus_imp_cp (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h : HasKrausRepresentation Φ) : IsCompletelyPositive Φ := by
  classical
  obtain ⟨r, A, hA⟩ := h
  intro k _ X hX
  have hEq : ampliation Φ k X =
      ∑ s, (Matrix.of fun (u : n × k) (v : m × k) =>
              A s u.1 v.1 * (if u.2 = v.2 then 1 else 0) : Matrix (n × k) (m × k) ℂ) * X *
            (Matrix.of fun (u : n × k) (v : m × k) =>
              A s u.1 v.1 * (if u.2 = v.2 then 1 else 0) : Matrix (n × k) (m × k) ℂ)ᴴ := by
    ext p q
    rw [ampliation, Matrix.of_apply, hA, Matrix.sum_apply, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type, RCLike.star_def, apply_ite, map_zero, Finset.sum_mul,
      ite_mul, zero_mul, mul_zero, mul_one, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hEq]
  exact posSemidef_sum _ _ fun s _ => hX.mul_mul_conjTranspose_same _

end KrausToCP

/-- **Choi–Jamiołkowski isomorphism**: a linear map between matrix algebras is completely
positive if and only if its Choi matrix is positive semidefinite. -/
