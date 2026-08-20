import Mathlib

/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
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

/-- The trace norm (sum of the absolute values of the eigenvalues) of the real diagonal
matrix `diagonal (fun i => cos (θ i))`. -/

theorem abs_trace_le_cosTraceNorm {n : ℕ} (θ : Fin n → ℝ) :
    |Matrix.trace (Matrix.diagonal fun i : Fin n => Real.cos (θ i))| ≤ cosTraceNorm θ := by
  simp only [Matrix.trace_diagonal, cosTraceNorm]
  exact Finset.abs_sum_le_sum_abs _ _

/-- The trace norm is bounded by the dimension, since `|cos| ≤ 1`. -/
