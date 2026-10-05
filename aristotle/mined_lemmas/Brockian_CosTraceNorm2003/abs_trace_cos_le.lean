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
open scoped MatrixOrder

namespace Brockian

open Matrix

/-- The *cosine Gram matrix* of a family of phases `θ : Fin n → ℝ`:
its `(i, j)` entry is `cos (θ i - θ j)`. -/

theorem abs_trace_cos_le {n : ℕ} (f : Fin n → Fin n → ℝ) :
    |(Matrix.of fun i j => Real.cos (f i j)).trace| ≤ (n : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin n, |Real.cos (f i i)| ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (n : ℝ) := by simp

end Brockian
#print axioms Brockian.CosTraceNorm2003

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

