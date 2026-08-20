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

namespace Brockian

open Matrix

/-- The trace norm (Schatten `1`-norm) of a Hermitian complex matrix: the sum of the absolute
values of its eigenvalues.  (It is set to `0` on non-Hermitian matrices, which we never use.) -/

theorem cosKernel_trace {N m : ℕ} (c w : Fin m → ℝ) (x : Fin N → ℝ) :
    (cosKernel c w x).trace = ((N : ℂ) * ((∑ k, c k : ℝ) : ℂ)) := by
  simp [Matrix.trace, Matrix.diag, cosKernel, Finset.sum_const, nsmul_eq_mul]

/-- **Trace-norm bound for cosine kernel matrices.**
For nonnegative weights `c k`, arbitrary frequencies `w k` and arbitrary nodes `x i`, the
`N × N` matrix with entries `∑ k, c k * cos (w k * (x i - x j))` has trace norm exactly
`N * ∑ k, c k`; in particular this is a sharp upper bound. -/
