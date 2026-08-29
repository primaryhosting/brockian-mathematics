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

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The "cosine trace" of a Hermitian matrix `A`: the trace of `cos A`, computed
through the spectral decomposition as the sum of `cos` of the eigenvalues. -/
noncomputable def cosTrace {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, Real.cos (hA.eigenvalues i)

/-- The trace norm (Schatten 1-norm) of a Hermitian matrix: the sum of its singular
values, which for a Hermitian matrix are the absolute values of the eigenvalues. -/
noncomputable def traceNorm {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The squared Hilbert–Schmidt (Frobenius) norm of a Hermitian matrix, computed
spectrally as the sum of the squares of its eigenvalues. -/
noncomputable def hsNormSq {A : Matrix n n ℂ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, (hA.eigenvalues i) ^ 2

/-- Pointwise bound: `1 - cos x ≤ |x|` for every real `x`. -/
lemma one_sub_cos_le_abs (x : ℝ) : 1 - Real.cos x ≤ |x| := by
  have h : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have := Real.cos_sq_half x
    nlinarith [Real.sin_sq_add_cos_sq (x / 2), Real.cos_sq_half x,
      Real.sin_sq_half_eq_one_sub_cos x]
  rw [h]
  have h1 : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  have h2 : Real.sin (x / 2) ^ 2 = |Real.sin (x / 2)| ^ 2 := (sq_abs _).symm
  have h3 : |Real.sin (x / 2)| ≤ 1 := Real.abs_sin_le_one _
  have h4 : |x / 2| = |x| / 2 := by
    rw [abs_div]; simp
  nlinarith [abs_nonneg (Real.sin (x / 2)), abs_nonneg x]

/-- Pointwise bound: `1 - cos x ≤ x ^ 2 / 2` for every real `x`. -/
lemma one_sub_cos_le_sq_div_two (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

/--
**Cos Trace Norm 2003.**

For a Hermitian matrix `A` of size `n`, writing `cosTrace A = Tr(cos A)`,
`‖A‖₁` for the trace norm and `‖A‖₂²` for the squared Hilbert–Schmidt norm:

* `|Tr(cos A)| ≤ n`;
* `0 ≤ n - Tr(cos A)`;
* `n - Tr(cos A) ≤ ‖A‖₁` (a new trace-norm bound);
* `n - Tr(cos A) ≤ ‖A‖₂² / 2`.
-/
theorem CosTraceNorm2003 {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    |cosTrace hA| ≤ (Fintype.card n : ℝ) ∧
    0 ≤ (Fintype.card n : ℝ) - cosTrace hA ∧
    (Fintype.card n : ℝ) - cosTrace hA ≤ traceNorm hA ∧
    (Fintype.card n : ℝ) - cosTrace hA ≤ hsNormSq hA / 2 := by
  have hcard : (Fintype.card n : ℝ) = ∑ _i : n, (1 : ℝ) := by
    simp [Fintype.card]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc |cosTrace hA| ≤ ∑ i, |Real.cos (hA.eigenvalues i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : n, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact Real.abs_cos_le_one _
      _ = (Fintype.card n : ℝ) := hcard.symm
  · have : cosTrace hA ≤ ∑ _i : n, (1 : ℝ) :=
      Finset.sum_le_sum fun i _ => Real.cos_le_one _
    rw [hcard]; linarith
  · have h : (∑ _i : n, (1 : ℝ)) - cosTrace hA ≤ traceNorm hA := by
      rw [cosTrace, traceNorm, ← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum fun i _ => one_sub_cos_le_abs _
    rw [hcard]; exact h
  · have h : (∑ _i : n, (1 : ℝ)) - cosTrace hA ≤ hsNormSq hA / 2 := by
      rw [cosTrace, hsNormSq, ← Finset.sum_sub_distrib, ← Finset.sum_div]
      exact Finset.sum_le_sum fun i _ => one_sub_cos_le_sq_div_two _
    rw [hcard]; exact h

end Brockian

