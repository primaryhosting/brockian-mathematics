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
noncomputable def frobNorm (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (trace (Aᵀ * A))

lemma trace_transpose_self_nonneg (A : Matrix (Fin n) (Fin n) ℝ) :
    0 ≤ trace (Aᵀ * A) := by
  rw [trace_transpose_mul_eq_sum]
  exact Finset.sum_nonneg fun p _ => mul_self_nonneg _

lemma frobNorm_nonneg (A : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ frobNorm A :=
  Real.sqrt_nonneg _

lemma frobNorm_sq (A : Matrix (Fin n) (Fin n) ℝ) :
    frobNorm A ^ 2 = trace (Aᵀ * A) :=
  Real.sq_sqrt (trace_transpose_self_nonneg A)

/-- Cauchy–Schwarz for the Frobenius inner product of real matrices. -/
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
theorem CosTraceNorm3001 (A B : Matrix (Fin n) (Fin n) ℝ) :
    ∃ θ : ℝ, trace (Aᵀ * B) = Real.cos θ * (frobNorm A * frobNorm B) ∧
      |trace (Aᵀ * B)| ≤ frobNorm A * frobNorm B := by
  have hbound := abs_trace_transpose_mul_le A B
  have hprod : 0 ≤ frobNorm A * frobNorm B :=
    mul_nonneg (frobNorm_nonneg A) (frobNorm_nonneg B)
  rcases eq_or_lt_of_le hprod with h0 | hpos
  · refine ⟨Real.pi / 2, ?_, hbound⟩
    have : trace (Aᵀ * B) = 0 := by
      have := hbound
      rw [← h0] at this
      exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))
    rw [this, ← h0]
    ring
  · set t : ℝ := trace (Aᵀ * B) / (frobNorm A * frobNorm B) with ht
    have habs : |t| ≤ 1 := by
      rw [ht, abs_div, abs_of_nonneg hprod]
      exact div_le_one_of_le₀ hbound hprod
    have h1 : -1 ≤ t := neg_le_of_abs_le habs
    have h2 : t ≤ 1 := le_of_abs_le habs
    refine ⟨Real.arccos t, ?_, hbound⟩
    rw [Real.cos_arccos h1 h2, ht, div_mul_cancel₀ _ (ne_of_gt hpos)]

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

