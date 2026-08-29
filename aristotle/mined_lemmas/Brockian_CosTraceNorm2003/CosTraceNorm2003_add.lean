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

theorem CosTraceNorm2003_add (n m : ℕ) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    nuclearNorm (Matrix.of fun (j : Fin n) (k : Fin m) => Real.cos (x j + y k)) ≤
      Real.sqrt (n * m) := by
  have h := CosTraceNorm2003 n m x (fun k => -y k)
  simpa [sub_neg_eq_add] using h

/-- Sharpness of `CosTraceNorm2003`: for the square Gram-type cosine matrix
`A j k = cos (x j - x k)` the bound `√(n·n) = n` is attained. -/
