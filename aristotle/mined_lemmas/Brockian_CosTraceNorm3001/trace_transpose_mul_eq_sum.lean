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

lemma trace_transpose_mul_eq_sum (A B : Matrix (Fin n) (Fin n) ℝ) :
    trace (Aᵀ * B) = ∑ p : Fin n × Fin n, A p.1 p.2 * B p.1 p.2 := by
  simp only [trace, diag_apply, mul_apply, transpose_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- The Frobenius norm, as the square root of the trace of `Aᵀ * A`. -/
