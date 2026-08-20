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

theorem sum_sq_eigenvalues (hA : A.IsHermitian) :
    ∑ i, (hA.eigenvalues i) ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  have h := trace_cfc_eq_sum_eigenvalues hA (fun x : ℝ => x ^ 2)
  rw [cfc_sq hA, trace_sq_eq_sum_normSq hA] at h
  exact_mod_cast h.symm

/-- **A trace-norm bound for the matrix cosine.**

For a Hermitian complex matrix `A` of size `n`, the cosine `cos A`, defined by the continuous
functional calculus, has trace within `‖A‖_F ^ 2 / 2` of `n`, where `‖A‖_F ^ 2 = ∑ i j, ‖A i j‖ ^ 2`
is the squared Frobenius (Hilbert–Schmidt) norm of `A`. -/
