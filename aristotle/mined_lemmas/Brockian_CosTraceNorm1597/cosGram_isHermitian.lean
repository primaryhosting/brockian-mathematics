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

lemma cosGram_isHermitian (x : n → ℝ) : (cosGram x).IsHermitian :=
  (cosGram_posSemidef x).isHermitian

omit [DecidableEq n] in
/-- The trace of the cosine Gram matrix is the size of the index set. -/
