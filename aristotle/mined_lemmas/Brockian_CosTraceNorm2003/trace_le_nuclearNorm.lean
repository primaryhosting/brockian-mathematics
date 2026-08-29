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

lemma trace_le_nuclearNorm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.trace ≤ nuclearNorm A := by
  refine le_csInf (nuclearBounds_nonempty A) ?_
  rintro c ⟨r, u, v, hA, hc⟩
  refine le_trans ?_ hc
  have htr : A.trace = ∑ i : Fin r, ∑ j : Fin n, u i j * v i j := by
    rw [Matrix.trace]
    simp only [Matrix.diag]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hA j j
  rw [htr]
  exact Finset.sum_le_sum fun i _ => sum_mul_le_sqrt_mul_sqrt (u i) (v i)

/-- Key two-term Cauchy–Schwarz estimate behind the cosine bound. -/
