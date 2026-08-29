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

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix, defined as the sum of the
absolute values of its eigenvalues (and `0` on non-Hermitian matrices). -/

theorem CosTraceNorm2003_unit (θ : n → ℝ) :
    traceNorm (cosGram (fun _ => (1 : ℝ)) θ) = (Fintype.card n : ℝ) := by
  rw [CosTraceNorm2003]
  simp [Finset.card_univ]

/-- Consequently the trace norm of any such cosine Gram matrix is bounded by
`(Fintype.card n) * (sup of the squared weights)`. -/
