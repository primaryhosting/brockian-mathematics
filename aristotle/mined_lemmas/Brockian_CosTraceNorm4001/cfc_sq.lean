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

theorem cfc_sq (hA : A.IsHermitian) : cfc (fun x : ℝ => x ^ 2) A = A ^ 2 := by
  have h : IsSelfAdjoint A := hA
  rw [cfc_pow (R := ℝ) (a := A) (f := fun x : ℝ => x) 2]
  congr 1
  simpa using cfc_id ℝ A

/-- The sum of the squares of the eigenvalues of a Hermitian matrix equals its squared
Frobenius norm. -/
