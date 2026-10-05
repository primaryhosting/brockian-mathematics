/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped Matrix

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

section CosTraceNorm

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute
values of its eigenvalues. -/

theorem hermTraceNorm_cosGram_le (x : n → ℝ) :
    hermTraceNorm (cosGram_isHermitian x) ≤ (Fintype.card n : ℝ) :=
  le_of_eq (hermTraceNorm_cosGram x)

end CosTraceNorm

/-- **Cos Trace Norm 1597.** For any 1597 phases `x : Fin 1597 → ℝ`, the trace norm
(sum of absolute values of eigenvalues) of the positive semidefinite cosine Gram matrix
`M i j = cos (x i - x j)` equals `1597`. -/
