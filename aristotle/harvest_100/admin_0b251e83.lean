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

/-
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
open scoped Classical

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of the absolute values of
its eigenvalues. -/
noncomputable def specTraceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The trace of `cos A` for a Hermitian matrix `A`, computed through the spectrum:
`∑ i, cos (μ i)` where the `μ i` are the eigenvalues of `A`. -/
noncomputable def cosTrace {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, Real.cos (hA.eigenvalues i)

/-- The Hilbert-Schmidt (Frobenius) norm squared of a Hermitian matrix, through the spectrum. -/
noncomputable def specHSNormSq {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, hA.eigenvalues i ^ 2

section Pointwise

/-- `1 - cos x` is nonnegative. -/
theorem one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  have := Real.cos_le_one x
  linarith

/-- `1 - cos x ≤ |x|`: the cosine is 1-Lipschitz. -/
theorem one_sub_cos_le_abs (x : ℝ) : 1 - Real.cos x ≤ |x| := by
  have h := Real.abs_cos_sub_cos_le 0 x
  simp only [Real.cos_zero, zero_sub, abs_neg] at h
  calc 1 - Real.cos x ≤ |1 - Real.cos x| := le_abs_self _
    _ ≤ |x| := by simpa [abs_sub_comm] using h

/-- `1 - cos x ≤ x ^ 2 / 2`. -/
theorem one_sub_cos_le_sq_div_two (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

end Pointwise

/-- The absolute value of the trace of a Hermitian matrix is bounded by its trace norm. -/
theorem norm_trace_le_specTraceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    ‖A.trace‖ ≤ specTraceNorm hA := by
  rw [hA.trace_eq_sum_eigenvalues]
  calc ‖∑ i, ((hA.eigenvalues i : ℝ) : ℂ)‖ ≤ ∑ i, ‖((hA.eigenvalues i : ℝ) : ℂ)‖ :=
        norm_sum_le _ _
    _ = specTraceNorm hA := by
        simp [specTraceNorm, Complex.norm_real, Real.norm_eq_abs]

/-- The cosine trace is bounded in absolute value by the dimension. -/
theorem abs_cosTrace_le_card {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    |cosTrace hA| ≤ (Fintype.card n : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |Real.cos (hA.eigenvalues i)| ≤ ∑ _i : n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => Real.abs_cos_le_one _
    _ = (Fintype.card n : ℝ) := by simp [Finset.card_univ]

/-- **Cos Trace Norm 2003.**  For a Hermitian matrix `A` of size `n`, the defect
`n - Tr cos A` is nonnegative and is dominated both by the trace norm `‖A‖₁` of `A`
and by half of its squared Hilbert–Schmidt norm. -/
theorem CosTraceNorm2003 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    0 ≤ (Fintype.card n : ℝ) - cosTrace hA ∧
      (Fintype.card n : ℝ) - cosTrace hA ≤ specTraceNorm hA ∧
      (Fintype.card n : ℝ) - cosTrace hA ≤ specHSNormSq hA / 2 := by
  have hcard : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by simp [Finset.card_univ]
  have hdiff : (Fintype.card n : ℝ) - cosTrace hA
      = ∑ i, (1 - Real.cos (hA.eigenvalues i)) := by
    rw [hcard, cosTrace, ← Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_⟩
  · rw [hdiff]
    exact Finset.sum_nonneg fun i _ => one_sub_cos_nonneg _
  · rw [hdiff, specTraceNorm]
    exact Finset.sum_le_sum fun i _ => one_sub_cos_le_abs _
  · rw [hdiff, specHSNormSq, Finset.sum_div]
    exact Finset.sum_le_sum fun i _ => one_sub_cos_le_sq_div_two _

end Brockian

