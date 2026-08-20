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

theorem IsCompletelyPositive.choi_posSemidef {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (h : IsCompletelyPositive Φ) : (choi Φ).PosSemidef := by
  classical
  set N := Fintype.card n with hN
  set e : n ≃ Fin N := Fintype.equivFin n with he
  -- the (unnormalised) maximally entangled state `Ω = |ω⟩⟨ω|`
  set v : (Fin N × n) → ℂ := fun x => if e.symm x.1 = x.2 then 1 else 0 with hv
  set A : Matrix (Fin N × n) Unit ℂ := Matrix.of fun x _ => v x with hA
  set Ω : Matrix (Fin N × n) (Fin N × n) ℂ := A * Aᴴ with hΩ
  have hΩpsd : Ω.PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (Aᴴ)
    simpa [hΩ] using this
  have key : ampliation (Fin N) Φ Ω =
      (choi Φ).submatrix (fun x => (e.symm x.1, x.2)) (fun x => (e.symm x.1, x.2)) := by
    ext p q
    have hblock : (Matrix.of fun i j => Ω (p.1, i) (q.1, j))
        = Matrix.single (e.symm p.1) (e.symm q.1) (1 : ℂ) := by
      ext i j
      simp only [hΩ, hA, hv, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply,
        Matrix.single_apply, Finset.univ_unique, Finset.sum_const, Finset.card_singleton,
        one_smul]
      split_ifs with h1 <;> simp_all
    simp only [ampliation, choi, Matrix.submatrix_apply, Matrix.of_apply, hblock]
  have hamp := h N Ω hΩpsd
  rw [key] at hamp
  have h2 := hamp.submatrix (fun x : n × m => (e x.1, x.2))
  rw [Matrix.submatrix_submatrix] at h2
  simpa [Function.comp_def] using h2

open scoped MatrixOrder in
/-- A map with positive semidefinite Choi matrix admits a Kraus decomposition. -/
