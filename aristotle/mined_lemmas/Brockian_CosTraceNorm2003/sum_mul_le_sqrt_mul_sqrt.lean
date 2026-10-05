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

lemma sum_mul_le_sqrt_mul_sqrt {n : ℕ} (f g : Fin n → ℝ) :
    ∑ j, f j * g j ≤ Real.sqrt (∑ j, (f j) ^ 2) * Real.sqrt (∑ j, (g j) ^ 2) := by
  have h1 : (∑ j, f j * g j) ^ 2 ≤ (∑ j, (f j) ^ 2) * (∑ j, (g j) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul (by positivity)] at h2
  exact le_trans (le_abs_self _) h2

/-- The trace of a square matrix is a lower bound for its nuclear norm. -/
