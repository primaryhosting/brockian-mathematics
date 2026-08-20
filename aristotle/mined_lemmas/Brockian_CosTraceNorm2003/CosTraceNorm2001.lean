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

theorem CosTraceNorm2001 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖A.trace‖ ≤ traceNorm hA := by
  have h := CosTraceNorm2002 (U := (1 : Matrix n n ℂ)) hA (by simp)
  simpa using h

omit [DecidableEq n] in
/-- The trace of a Hermitian matrix is real. -/
