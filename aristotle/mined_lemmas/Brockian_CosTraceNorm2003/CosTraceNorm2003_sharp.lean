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

theorem CosTraceNorm2003_sharp (n : ℕ) (x : Fin n → ℝ) :
    nuclearNorm (Matrix.of fun (j k : Fin n) => Real.cos (x j - x k)) = (n : ℝ) := by
  refine le_antisymm ?_ ?_
  · have h := CosTraceNorm2003 n n x x
    rwa [show ((n : ℝ) * n) = (n : ℝ) ^ 2 by ring, Real.sqrt_sq (Nat.cast_nonneg n)] at h
  · have h := trace_le_nuclearNorm (Matrix.of fun (j k : Fin n) => Real.cos (x j - x k))
    have htr : (Matrix.of fun (j k : Fin n) => Real.cos (x j - x k)).trace = (n : ℝ) := by
      simp [Matrix.trace, Matrix.diag]
    rwa [htr] at h

end Brockian

