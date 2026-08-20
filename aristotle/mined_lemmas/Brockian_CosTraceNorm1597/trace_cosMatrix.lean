/-
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian

/-- The `n × n` real "cosine Hankel" matrix with entries `cos (θ * (i + j))`. -/

lemma trace_cosMatrix (θ : ℝ) (n : ℕ) :
    Matrix.trace (cosMatrix θ n) = ∑ k ∈ Finset.range n, Real.cos (2 * θ * k) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => Real.cos (2 * θ * k)) n, Matrix.trace]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp only [Matrix.diag_apply, cosMatrix, Matrix.of_apply]
  ring_nf

/-- Telescoping identity: `sin θ · ∑_{k<n} cos (2θk) = (sin ((2n-1)θ) + sin θ)/2`. -/
