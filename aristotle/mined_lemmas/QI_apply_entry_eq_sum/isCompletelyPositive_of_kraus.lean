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

lemma isCompletelyPositive_of_kraus (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ)
    {r : Type} [Fintype r] (K : r → Matrix m n ℂ)
    (hK : ∀ X : Matrix n n ℂ, Φ X = ∑ s, K s * X * (K s)ᴴ) : IsCompletelyPositive Φ := by
  intro k _ _ A hA
  set M : r → Matrix (m × k) (n × k) ℂ :=
    fun s => Matrix.of fun p q => if p.2 = q.2 then K s p.1 q.1 else 0 with hMdef
  have key : (Matrix.of fun p q : m × k => Φ (Matrix.of fun i j => A (i, p.2) (j, q.2)) p.1 q.1)
      = ∑ s, M s * A * (M s)ᴴ := by
    ext p q
    obtain ⟨a, s0⟩ := p
    obtain ⟨b, t0⟩ := q
    rw [Matrix.sum_apply]
    simp only [Matrix.of_apply, hK, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hMdef, Matrix.of_apply,
      Fintype.sum_prod_type, ite_mul, zero_mul, apply_ite (star : ℂ → ℂ), star_zero, mul_ite,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [key]
  exact Finset.sum_induction _ _ (fun x y hx hy => hx.add hy) Matrix.PosSemidef.zero
    (fun s _ => hA.mul_mul_conjTranspose_same (M s))

omit [DecidableEq m] in
/-- If the Choi matrix of `Φ` is positive semidefinite, then `Φ` admits a Kraus decomposition. -/
