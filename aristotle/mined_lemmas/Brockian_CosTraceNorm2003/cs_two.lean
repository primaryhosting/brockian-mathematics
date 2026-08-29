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
open scoped Real

set_option maxHeartbeats 1000000

namespace Brockian

/-- The set of admissible bounds for the nuclear (trace) norm of a real matrix `A`:
`c` belongs to it iff `A` can be written as a finite sum of rank-one matrices
`u i ⊗ v i` whose total "product of Euclidean norms" is at most `c`. -/

lemma cs_two (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a * c + b * d ≤ Real.sqrt ((a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2)) := by
  have h : (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by nlinarith [sq_nonneg (a*d - b*c)]
  have h2 := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq (by positivity)] at h2

/-- **Cos Trace Norm 2003.**
For arbitrary real phases `x : Fin n → ℝ` and `y : Fin m → ℝ`, the `n × m` cosine matrix
`A j k = cos (x j - y k)` has nuclear (trace) norm at most `√(n·m)`. -/
