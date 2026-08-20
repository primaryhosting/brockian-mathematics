/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Matrix

variable {n : ℕ}

/-- The Frobenius (Hilbert–Schmidt) inner product of two real matrices, written as a
trace, is the sum of the entrywise products. -/

lemma trace_transpose_self_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ trace (Aᵀ * A) := by
  rw [trace_transpose_mul_eq_sum]
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg _

