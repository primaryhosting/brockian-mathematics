/-
/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

open scoped BigOperators
open scoped Real

namespace Brockian

/-- The `n × n` real diagonal matrix whose `i`-th diagonal entry is `cos (θ * i)`. -/
noncomputable def cosDiag (n : ℕ) (θ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i : Fin n => Real.cos (θ * i))

/-- The trace of `cosDiag n θ` is the cosine sum `∑ i < n, cos (θ * i)`. -/
theorem trace_cosDiag (n : ℕ) (θ : ℝ) :
    (cosDiag n θ).trace = ∑ i : Fin n, Real.cos (θ * i) := by
  simp [cosDiag, Matrix.trace_diagonal]

/--
**Cos Trace Norm 1597.**

For the diagonal cosine matrix `cosDiag n θ` (diagonal entries `cos (θ * i)`, `i < n`):

* the absolute value of its trace is bounded by its trace norm, i.e. by the sum of the
  absolute values of its (diagonal) singular values;
* that trace norm is at most `n`;
* the bound is sharp: at `θ = 0` the trace itself equals `n`.

The key Mathlib ingredients are `Finset.abs_sum_le_sum_abs` and `Real.abs_cos_le_one`.
-/
theorem CosTraceNorm1597 (n : ℕ) (θ : ℝ) :
    |(cosDiag n θ).trace| ≤ ∑ i : Fin n, |Real.cos (θ * i)| ∧
      (∑ i : Fin n, |Real.cos (θ * i)|) ≤ n ∧
      (cosDiag n 0).trace = n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [trace_cosDiag]
    exact Finset.abs_sum_le_sum_abs _ _
  · calc (∑ i : Fin n, |Real.cos (θ * i)|) ≤ ∑ _i : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum (fun i _ => Real.abs_cos_le_one (θ * i))
      _ = n := by simp
  · rw [trace_cosDiag]
    simp

end Brockian

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

