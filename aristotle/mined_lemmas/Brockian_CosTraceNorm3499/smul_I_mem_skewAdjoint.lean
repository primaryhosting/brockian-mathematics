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

namespace Brockian

open NormedSpace
open scoped Matrix Matrix.Norms.Operator

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix cosine of a complex square matrix, defined through the matrix exponential by
`cos A = (exp (i A) + exp (-i A)) / 2`. -/

lemma smul_I_mem_skewAdjoint {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Complex.I • A ∈ skewAdjoint (Matrix n n ℂ) := by
  rw [skewAdjoint.mem_iff, star_smul, Matrix.star_eq_conjTranspose, hA.eq]
  simp

/-- For Hermitian `A`, the matrix `exp (i A)` is unitary. -/
