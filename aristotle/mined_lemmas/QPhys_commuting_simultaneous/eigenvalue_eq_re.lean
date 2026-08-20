import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open Module Module.End LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- If `A` and `B` commute, then `B` maps each eigenspace of `A` into itself. -/

lemma eigenvalue_eq_re {A : E →ₗ[ℂ] E} (hA : A.IsSymmetric) {mu : ℂ}
    (hmu : HasEigenvalue A mu) : ((mu.re : ℝ) : ℂ) = mu := by
  have h := hA.conj_eigenvalue_eq_self hmu
  have him : mu.im = 0 := by
    have := congrArg Complex.im h
    simp at this
    linarith
  simp [Complex.ext_iff, him]

/-- **Two commuting Hermitian (self-adjoint) operators on a finite-dimensional complex inner
product space are simultaneously diagonalizable**: there is an orthonormal basis of the space
consisting of vectors that are simultaneously eigenvectors of both operators, with real
eigenvalues. -/
