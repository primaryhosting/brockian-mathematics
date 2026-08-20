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

import RequestProject.QI.KadisonSchwarz

/-!
# A variational formula for the resolvent quantity `G`

For positive semidefinite `ρ`, `σ` and `t ≥ 0` we consider the concave functional

`energy ρ σ t X = 2 Re Tr (ρ X) - Re Tr (Xᴴ σ X) - t Re Tr (Xᴴ X ρ)`

and its supremum `Gfun ρ σ t`.  This is a variational form of
`⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫` for the relative modular operator `Δ : Z ↦ σ Z ρ⁻¹`.

Two facts are proved here:

* `Gfun` is computed by any stationary point (`Gfun_eq_of_stationary`), and a stationary
  point exists whenever `σ` is positive definite, with an explicit spectral value
  (`Gfun_spectral`);
* `Gfun` is monotone under quantum channels (`Gfun_krausMap_le`).
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- The concave functional whose supremum is `Gfun`. -/

theorem krausDual_eq_stack (K : ι → Matrix m n ℂ) (X : Matrix m m ℂ) :
    krausDual K X = (krausStack K)ᴴ * (Matrix.blockDiagonal fun _ : ι => X) * (krausStack K) := by
  ext b c
  simp only [krausDual, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    krausStack, Matrix.of_apply, Matrix.blockDiagonal_apply, Fintype.sum_prod_type,
    Finset.sum_mul, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]

/-- **Kadison–Schwarz inequality** for the adjoint of a trace preserving Kraus channel. -/
