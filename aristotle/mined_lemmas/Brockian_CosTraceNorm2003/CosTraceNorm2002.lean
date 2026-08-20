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

/-!
# The `CosTraceNorm` family: trace-norm bounds for Hermitian matrices

For a Hermitian matrix `A` the *trace norm* (Schatten 1-norm) `‖A‖₁` is the sum of the absolute
values of its eigenvalues.  This file develops a small family of bounds for it:

* `Brockian.CosTraceNorm2001` : `|Tr A| ≤ ‖A‖₁`;
* `Brockian.CosTraceNorm2002` : the dual (Hölder-type) bound `|Tr (A U)| ≤ ‖A‖₁` for `U` unitary;
* `Brockian.CosTraceNorm2003` : a new cosine-parametrised bound.  If `B` is a Hermitian unitary
  (a reflection), then for every angle `t`,
  `√((cos t · Tr A)² + (sin t · Tr (A B))²) ≤ ‖A‖₁`,
  i.e. the point `(Tr A, Tr (A B))` lies inside every ellipse `x²/sec²t + y²/csc²t = ‖A‖₁²`.
-/

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The **trace norm** (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values
of its eigenvalues. -/

theorem CosTraceNorm2002 {A U : Matrix n n ℂ} (hA : A.IsHermitian) (hU : Uᴴ * U = 1) :
    ‖(A * U).trace‖ ≤ traceNorm hA := by
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self _
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self _
  set D : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD
  have hspec : A = V * D * star V := hA.spectral_theorem
  set W : Matrix n n ℂ := star V * U * V with hW
  have hstarW : star W = star V * star U * V := by
    rw [hW, Matrix.star_mul, Matrix.star_mul, star_star, mul_assoc]
  have hWu : Wᴴ * W = 1 := by
    have h1 : (Wᴴ : Matrix n n ℂ) = star W := rfl
    rw [h1, hstarW, hW]
    calc star V * star U * V * (star V * U * V)
        = star V * star U * (V * star V) * U * V := by simp [mul_assoc]
      _ = star V * (star U * U) * V := by rw [hVV']; simp [mul_assoc]
      _ = 1 := by rw [show (star U : Matrix n n ℂ) = Uᴴ from rfl, hU]; simpa using hVV
  have htr : (A * U).trace = (D * W).trace := by
    rw [hspec, hW, show V * D * star V * U = V * (D * star V * U) by simp [mul_assoc],
      Matrix.trace_mul_comm]
    congr 1
    simp [mul_assoc]
  rw [htr, hD, traceNorm]
  exact norm_trace_diagonal_mul_le _ (norm_diag_le_one_of_unitary hWu)

/-- `CosTraceNorm2001`: the trace of a Hermitian matrix is bounded by its trace norm. -/
