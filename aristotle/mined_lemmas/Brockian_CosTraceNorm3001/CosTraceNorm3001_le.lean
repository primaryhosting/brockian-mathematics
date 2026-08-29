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

set_option grind.warning false

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The cosine matrix associated to a family of phases `θ`: its `(i, j)` entry is
`cos (θ i - θ j)`. -/

theorem CosTraceNorm3001_le (θ : n → ℝ) :
    hermTraceNorm (cosMatrix θ) ≤ Fintype.card n :=
  le_of_eq (CosTraceNorm3001 θ)

end Brockian

#print axioms Brockian.CosTraceNorm3001
#print axioms Brockian.CosTraceNorm3001_le

