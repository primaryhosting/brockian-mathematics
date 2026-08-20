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

set_option grind.warning false

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}

/-- The trace of `cfc f A`, for a Hermitian matrix `A`, is the sum of `f` over the
eigenvalues of `A`. -/

theorem trace_sq_eq_sum_normSq (hA : A.IsHermitian) :
    (A ^ 2).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  rw [pow_two, Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h : A j i = star (A i j) := by
    have := hA.apply j i
    simpa [Matrix.IsHermitian] using this.symm
  rw [h]
  push_cast
  exact Complex.mul_conj' (A i j)

/-- The functional calculus applied to `x ↦ x ^ 2` returns the square of the matrix. -/
