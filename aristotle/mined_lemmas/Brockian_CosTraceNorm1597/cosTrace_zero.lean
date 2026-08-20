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

/-- The "cosine trace" of the regular representation at angle `x`:
`∑_{k < n} cos (k * x)`. -/

theorem cosTrace_zero (n : ℕ) : cosTrace n 0 = n := by
  simp [cosTrace]

/--
**Cos Trace Norm 1597.**

For the dimension `n = 1597`:

* the cosine trace `x ↦ ∑_{k < 1597} cos (k x)` is bounded in absolute value by `1597`;
* this bound is sharp, being attained at `x = 0`;
* at the primitive `1597`-th root of unity the trace vanishes:
  `∑_{k < 1597} cos (2πk/1597) = 0`.
-/
