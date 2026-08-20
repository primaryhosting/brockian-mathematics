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

theorem ampliation_kraus {k : Type} [Fintype k] [DecidableEq k]
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ) {r : ℕ} {K : Fin r → Matrix m n ℂ}
    (hK : ∀ X : Matrix n n ℂ, Φ X = ∑ a, K a * X * (K a)ᴴ)
    (X : Matrix (k × n) (k × n) ℂ) :
    ampliation k Φ X = ∑ a, (Matrix.of fun (p : k × m) (q : k × n) =>
      if p.1 = q.1 then K a p.2 q.2 else 0) * X *
      (Matrix.of fun (p : k × m) (q : k × n) => if p.1 = q.1 then K a p.2 q.2 else 0)ᴴ := by
  ext p q
  simp only [ampliation, Matrix.of_apply, hK, Matrix.sum_apply,
    blockDiag_mul_mul_conjTranspose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq n] [DecidableEq m] in
/-- A map with a Kraus decomposition is completely positive. -/
