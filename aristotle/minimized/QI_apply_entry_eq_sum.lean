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

lemma apply_entry_eq_sum (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) (X : Matrix n n ℂ) (a b : m) :
    Φ X a b = ∑ i, ∑ j, X i j * Φ (Matrix.single i j 1) a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  have h : ∀ i j : n, Matrix.single i j (X i j) = X i j • Matrix.single (α := ℂ) i j 1 := by
    intro i j
    ext p q
    simp [Matrix.single_apply]
  simp only [h, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

omit [DecidableEq n] [DecidableEq m] in
/-- A map given by a Kraus decomposition `Φ X = ∑ s, K s * X * (K s)ᴴ` is completely positive. -/
