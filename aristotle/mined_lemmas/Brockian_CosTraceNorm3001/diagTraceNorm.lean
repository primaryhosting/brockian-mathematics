/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
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

/-- The real diagonal matrix whose `i`-th diagonal entry is `cos (θ i)`. -/

noncomputable def diagTraceNorm (n : ℕ) (d : Fin n → ℝ) : ℝ := ∑ i, |d i|

/-- **Cos trace norm bounds.** For the diagonal matrix `cosDiag n θ` with diagonal entries
`cos (θ i)`:

* the absolute value of its trace is at most its trace norm;
* its trace norm is at most `n`;
* the trace norm equals `n` exactly when every `cos (θ i)` is `±1`.
-/
