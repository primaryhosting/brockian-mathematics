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

noncomputable def hermTraceNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) : ℝ :=
  if h : A.IsHermitian then ∑ i, |h.eigenvalues i| else 0

/-- The `N × N` cosine kernel matrix attached to frequencies `w`, weights `c` and nodes `x`:
its `(i, j)` entry is `∑ k, c k * cos (w k * (x i - x j))`. -/
