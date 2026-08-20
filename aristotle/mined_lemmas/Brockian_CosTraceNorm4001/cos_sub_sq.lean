import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
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

/-- Product-to-sum expansion of `cos (a - b) ^ 2`. -/

private lemma cos_sub_sq (a b : ℝ) :
    Real.cos (a - b) ^ 2
      = (1 + (Real.cos (2 * a) * Real.cos (2 * b) + Real.sin (2 * a) * Real.sin (2 * b))) / 2 := by
  have h1 : Real.cos (2 * a - 2 * b)
      = Real.cos (2 * a) * Real.cos (2 * b) + Real.sin (2 * a) * Real.sin (2 * b) :=
    Real.cos_sub _ _
  have h2 : Real.cos (2 * (a - b)) = 2 * Real.cos (a - b) ^ 2 - 1 := Real.cos_two_mul _
  rw [show 2 * a - 2 * b = 2 * (a - b) by ring] at h1
  linarith

/-- The exact Frobenius (Hilbert–Schmidt) energy of the cosine kernel matrix
`M i j = cos (x i - x j)`:  it equals `n²/2` plus a nonnegative "power-spectrum" term. -/
