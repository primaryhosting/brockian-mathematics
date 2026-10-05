import Mathlib
/-!
# Cos Trace Norm 1279
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1279
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- The trace norm (Schatten 1-norm) of a real diagonal matrix: the sum of the
absolute values of its diagonal entries, which are exactly its singular values. -/
noncomputable def diagTraceNorm {n : ℕ} (d : Fin n → ℝ) : ℝ := ∑ i, |d i|

/-- Auxiliary bound, proved by induction on `n`: a sum of `n` values `|cos θ|` is at
most `n`. -/
theorem sum_abs_cos_le (θ : ℕ → ℝ) : ∀ n : ℕ,
    ∑ k ∈ Finset.range n, |Real.cos (θ k)| ≤ (n : ℝ) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc (∑ k ∈ Finset.range n, |Real.cos (θ k)|) + |Real.cos (θ n)|
          ≤ (n : ℝ) + 1 := add_le_add ih (Real.abs_cos_le_one _)
        _ = ((n + 1 : ℕ) : ℝ) := by push_cast; ring

/-- **Cos Trace Norm 1279.**

For any phases `θ : Fin n → ℝ` and the diagonal matrix `D` with entries `cos (θ i)`:

* the trace norm of `D` is at most `n`;
* the absolute trace of `D` is dominated by its trace norm;
* hence the absolute trace of `D` is at most `n`;
* and both bounds are attained by the identity matrix (all phases zero). -/
theorem CosTraceNorm1279 (n : ℕ) (θ : Fin n → ℝ) :
    diagTraceNorm (fun i => Real.cos (θ i)) ≤ (n : ℝ) ∧
      |(Matrix.diagonal fun i => Real.cos (θ i)).trace|
        ≤ diagTraceNorm (fun i => Real.cos (θ i)) ∧
      |(Matrix.diagonal fun i => Real.cos (θ i)).trace| ≤ (n : ℝ) ∧
      diagTraceNorm (fun _ : Fin n => Real.cos (0 : ℝ)) = (n : ℝ) ∧
      |(Matrix.diagonal fun _ : Fin n => Real.cos (0 : ℝ)).trace| = (n : ℝ) := by
  have hnorm : diagTraceNorm (fun i => Real.cos (θ i)) ≤ (n : ℝ) := by
    have h : diagTraceNorm (fun i => Real.cos (θ i))
        = ∑ k ∈ Finset.range n, |Real.cos (if h : k < n then θ ⟨k, h⟩ else 0)| := by
      rw [diagTraceNorm,
        Finset.sum_range fun k => |Real.cos (if h : k < n then θ ⟨k, h⟩ else 0)|]
      simp
    rw [h]
    exact sum_abs_cos_le _ n
  have htr : |(Matrix.diagonal fun i => Real.cos (θ i)).trace|
      ≤ diagTraceNorm (fun i => Real.cos (θ i)) := by
    rw [Matrix.trace_diagonal, diagTraceNorm]
    exact Finset.abs_sum_le_sum_abs _ _
  refine ⟨hnorm, htr, htr.trans hnorm, ?_, ?_⟩ <;> simp [diagTraceNorm]

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

