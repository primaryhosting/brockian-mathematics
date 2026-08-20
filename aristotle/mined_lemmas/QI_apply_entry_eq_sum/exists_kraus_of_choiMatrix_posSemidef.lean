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

namespace QI

open Matrix
open scoped ComplexOrder

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ`.
It is the block matrix `∑ i j, Eᵢⱼ ⊗ Φ Eᵢⱼ`, written entrywise as
`choiMatrix Φ (i, a) (j, b) = Φ (single i j 1) a b`. -/

lemma exists_kraus_of_choiMatrix_posSemidef (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    (h : (choiMatrix Φ).PosSemidef) :
    ∃ (N : ℕ) (K : Fin N → Matrix m n ℂ), ∀ X : Matrix n n ℂ, Φ X = ∑ s, K s * X * (K s)ᴴ := by
  obtain ⟨N, v, hv⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp h
  refine ⟨N, fun s => Matrix.of fun a i => v s (i, a), fun X => ?_⟩
  ext a b
  have hentry : ∀ i j : n, Φ (Matrix.single i j 1) a b
      = ∑ s : Fin N, v s (i, a) * star (v s (j, b)) := by
    intro i j
    have h2 := congrArg (fun M => M (i, a) (j, b)) hv
    simpa only [choiMatrix, Matrix.of_apply, Matrix.sum_apply, Matrix.vecMulVec_apply,
      Pi.star_apply] using h2
  have hRHS : ∀ s : Fin N, ((Matrix.of fun a i => v s (i, a) : Matrix m n ℂ) * X *
        (Matrix.of fun a i => v s (i, a) : Matrix m n ℂ)ᴴ) a b
      = ∑ i, ∑ j, X i j * (v s (i, a) * star (v s (j, b))) := by
    intro s
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hswap : ∑ s : Fin N, ∑ i, ∑ j, X i j * (v s (i, a) * star (v s (j, b)))
      = ∑ i, ∑ j, ∑ s : Fin N, X i j * (v s (i, a) * star (v s (j, b))) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [apply_entry_eq_sum Φ X a b, Matrix.sum_apply]
  simp only [hRHS]
  rw [hswap]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [hentry i j, Finset.mul_sum]

/-- The (unnormalized) maximally entangled state `|ω⟩⟨ω|`, `ω = ∑ i, eᵢ ⊗ eᵢ`, is positive
semidefinite. -/
