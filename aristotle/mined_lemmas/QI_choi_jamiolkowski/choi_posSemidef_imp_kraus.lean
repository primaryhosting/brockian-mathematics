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

lemma choi_posSemidef_imp_kraus (Φ : Matrix m m ℂ →ₗ[ℂ] Matrix n n ℂ)
    (h : (choiMatrix Φ).PosSemidef) : HasKrausRepresentation Φ := by
  classical
  obtain ⟨B, hB⟩ := exists_conjTranspose_mul_self h
  set e := Fintype.equivFin (m × n) with he
  refine ⟨Fintype.card (m × n),
    fun s => Matrix.of fun k i => starRingEnd ℂ (B (e.symm s) (i, k)), ?_⟩
  intro X
  ext a b
  rw [apply_eq_sum Φ X a b, Matrix.sum_apply]
  have hC : ∀ i j : m, Φ (Matrix.single i j 1) a b
      = ∑ p : m × n, starRingEnd ℂ (B p (i, a)) * B p (j, b) := by
    intro i j
    have hij := congrFun (congrFun hB (i, a)) (j, b)
    simpa [choiMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply] using hij
  have swap3 : ∀ (g : (m × n) → m → m → ℂ),
      ∑ i, ∑ j, ∑ p, g p i j = ∑ p, ∑ i, ∑ j, g p i j := by
    intro g
    have h1 : ∀ i : m, ∑ j, ∑ p, g p i j = ∑ p, ∑ j, g p i j := fun _ => Finset.sum_comm
    simp_rw [h1]
    exact Finset.sum_comm
  have step1 : ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b
      = ∑ p : m × n, ∑ i, ∑ j, X i j * (starRingEnd ℂ (B p (i, a)) * B p (j, b)) := by
    simp_rw [hC, Finset.mul_sum]
    exact swap3 _
  rw [step1, ← Equiv.sum_comp e.symm
    (fun p : m × n => ∑ i, ∑ j, X i j * (starRingEnd ℂ (B p (i, a)) * B p (j, b)))]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, RCLike.star_def, Complex.conj_conj]
  ring

end ChoiToKraus

section KrausToCP

omit [DecidableEq m] [DecidableEq n] in
