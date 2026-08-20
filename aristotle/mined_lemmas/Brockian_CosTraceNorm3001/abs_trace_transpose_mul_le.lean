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

lemma abs_trace_transpose_mul_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    |trace (Aᵀ * B)| ≤ frobNorm A * frobNorm B := by
  have hcs :
      (∑ p : Fin n × Fin n, A p.1 p.2 * B p.1 p.2) ^ 2 ≤
        (∑ p : Fin n × Fin n, A p.1 p.2 ^ 2) * ∑ p : Fin n × Fin n, B p.1 p.2 ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hA : trace (Aᵀ * A) = ∑ p : Fin n × Fin n, A p.1 p.2 ^ 2 := by
    rw [trace_transpose_mul_eq_sum]; simp [sq]
  have hB : trace (Bᵀ * B) = ∑ p : Fin n × Fin n, B p.1 p.2 ^ 2 := by
    rw [trace_transpose_mul_eq_sum]; simp [sq]
  have hsq : trace (Aᵀ * B) ^ 2 ≤ (frobNorm A * frobNorm B) ^ 2 := by
    rw [mul_pow, frobNorm_sq, frobNorm_sq, hA, hB, trace_transpose_mul_eq_sum]
    exact hcs
  calc |trace (Aᵀ * B)| = Real.sqrt (trace (Aᵀ * B) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((frobNorm A * frobNorm B) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = frobNorm A * frobNorm B :=
        Real.sqrt_sq (mul_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B))

/-- **Cos Trace Norm 3001.**  For any two real square matrices `A`, `B` there is an angle
`θ` whose cosine realises the Frobenius (trace) inner product as
`trace (Aᵀ * B) = cos θ * ‖A‖_F * ‖B‖_F`, and consequently the trace-norm bound
`|trace (Aᵀ * B)| ≤ ‖A‖_F * ‖B‖_F` holds (Cauchy–Schwarz). -/
