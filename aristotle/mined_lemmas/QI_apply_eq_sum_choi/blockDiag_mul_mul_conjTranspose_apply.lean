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

theorem blockDiag_mul_mul_conjTranspose_apply {k : Type} [Fintype k] [DecidableEq k]
    (K : Matrix m n ℂ) (X : Matrix (k × n) (k × n) ℂ) (p q : k × m) :
    ((Matrix.of fun (p : k × m) (q : k × n) => if p.1 = q.1 then K p.2 q.2 else 0) * X *
      (Matrix.of fun (p : k × m) (q : k × n) => if p.1 = q.1 then K p.2 q.2 else 0)ᴴ) p q
      = ∑ i, ∑ j, K p.2 i * X (p.1, i) (q.1, j) * star (K q.2 j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, ite_mul, zero_mul, sum_prod_delta,
    apply_ite (star : ℂ → ℂ), star_zero, mul_ite, mul_zero, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [DecidableEq n] [Fintype m] [DecidableEq m] in
/-- The ampliation, expressed via the Kraus operators of `Φ`. -/
