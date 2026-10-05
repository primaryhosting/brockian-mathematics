/-
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian

open Matrix Finset

variable {n : ℕ}

/-- The "cosine matrix" attached to a list of phases `θ : Fin n → ℝ`:
the diagonal complex matrix with entries `cos (θ i)`. -/
noncomputable def cosDiag (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => (Real.cos (θ i) : ℂ)

/-- The trace norm (Schatten 1-norm) of the diagonal cosine matrix: the sum of the
absolute values of its diagonal entries, which are exactly its singular values. -/
noncomputable def cosTraceNorm (θ : Fin n → ℝ) : ℝ := ∑ i, |Real.cos (θ i)|

/-- Trace of the cosine matrix. -/
lemma trace_cosDiag (θ : Fin n → ℝ) :
    Matrix.trace (cosDiag θ) = ((∑ i, Real.cos (θ i) : ℝ) : ℂ) := by
  simp [cosDiag, Matrix.trace_diagonal]

/-- Unitary invariance of the trace of the cosine matrix. -/
lemma trace_unitary_conj_cosDiag (θ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    Matrix.trace (U * cosDiag θ * Uᴴ) = Matrix.trace (cosDiag θ) := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hU', Matrix.mul_one]

/-- The trace norm of the cosine matrix is at most the dimension. -/
lemma cosTraceNorm_le_dim (θ : Fin n → ℝ) : cosTraceNorm θ ≤ n := by
  have : ∀ i ∈ (Finset.univ : Finset (Fin n)), |Real.cos (θ i)| ≤ 1 := by
    intro i _; exact Real.abs_cos_le_one (θ i)
  calc cosTraceNorm θ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum this
    _ = n := by simp

/--
**Cos Trace Norm 3001.**

For any phases `θ : Fin n → ℝ` and any unitary `U`, the trace of the unitary conjugate
`U * cosDiag θ * Uᴴ` is unitarily invariant, is bounded in absolute value by the trace norm
`∑ i, |cos (θ i)|`, and the trace norm itself is bounded by the dimension `n`.
-/
theorem CosTraceNorm3001 (θ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) :
    Matrix.trace (U * cosDiag θ * Uᴴ) = Matrix.trace (cosDiag θ) ∧
      ‖Matrix.trace (U * cosDiag θ * Uᴴ)‖ ≤ cosTraceNorm θ ∧
      cosTraceNorm θ ≤ n := by
  refine ⟨trace_unitary_conj_cosDiag θ U hU, ?_, cosTraceNorm_le_dim θ⟩
  rw [trace_unitary_conj_cosDiag θ U hU, trace_cosDiag]
  calc ‖((∑ i, Real.cos (θ i) : ℝ) : ℂ)‖ = |∑ i, Real.cos (θ i)| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ i, |Real.cos (θ i)| := Finset.abs_sum_le_sum_abs _ _
    _ = cosTraceNorm θ := rfl

/-- Corollary: the trace of a unitary conjugate of the cosine matrix has norm at most `n`. -/
theorem norm_trace_cosDiag_le_dim (θ : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U * Uᴴ = 1) : ‖Matrix.trace (U * cosDiag θ * Uᴴ)‖ ≤ n := by
  obtain ⟨-, h₁, h₂⟩ := CosTraceNorm3001 θ U hU
  exact h₁.trans h₂

/-- Sharpness: the dimension bound is attained at the zero phases. -/
theorem cosTraceNorm_zero_eq_dim : cosTraceNorm (fun _ : Fin n => (0 : ℝ)) = n := by
  simp [cosTraceNorm]

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

