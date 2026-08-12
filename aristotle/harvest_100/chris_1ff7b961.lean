import Mathlib
import RequestProject.Brockian.CosTraceNorm3001

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

import Mathlib

/-!
# Trace-norm bounds for cosine Gram matrices (`CosTraceNorm` family)

For a family of angles `θ : Fin n → ℝ` we consider the *cosine matrix*

`cosMatrix θ i j = Real.cos (θ i - θ j)`.

It is the Gram matrix of the unit vectors `(cos (θ i), sin (θ i)) ∈ ℝ²`, hence real symmetric
and positive semidefinite, with all diagonal entries equal to `1`.

The main result `Brockian.CosTraceNorm3001` computes its Schatten `1`-norm (trace norm,
the sum of the absolute values of its eigenvalues): it is exactly `n`.  Because the matrix has
rank at most `2`, its Schatten `2`-norm (Frobenius norm) is at least `n / √2`, which is recorded
as a bound on `∑ i, ∑ j, cos (θ i - θ j) ^ 2`.
-/

open scoped BigOperators
open Matrix

namespace Brockian

variable {n : ℕ}

/-- The cosine matrix of a family of angles: `cosMatrix θ i j = cos (θ i - θ j)`. -/
noncomputable def cosMatrix (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => Real.cos (θ i - θ j)

/-- The `2 × n` matrix whose `j`-th column is the unit vector `(cos (θ j), sin (θ j))`. -/
noncomputable def circleMatrix (θ : Fin n → ℝ) : Matrix (Fin 2) (Fin n) ℝ :=
  Matrix.of fun k j => if k = 0 then Real.cos (θ j) else Real.sin (θ j)

/-- The cosine matrix is the Gram matrix of the unit vectors `(cos (θ i), sin (θ i))`. -/
theorem cosMatrix_eq_gram (θ : Fin n → ℝ) :
    cosMatrix θ = (circleMatrix θ)ᴴ * circleMatrix θ := by
  ext i j
  simp [cosMatrix, circleMatrix, Matrix.mul_apply, Fin.sum_univ_two, Real.cos_sub]

/-- The cosine matrix is positive semidefinite. -/
theorem cosMatrix_posSemidef (θ : Fin n → ℝ) : (cosMatrix θ).PosSemidef := by
  rw [cosMatrix_eq_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The cosine matrix is symmetric. -/
theorem cosMatrix_isHermitian (θ : Fin n → ℝ) : (cosMatrix θ).IsHermitian :=
  (cosMatrix_posSemidef θ).isHermitian

/-- The trace of the cosine matrix is `n`. -/
theorem cosMatrix_trace (θ : Fin n → ℝ) : (cosMatrix θ).trace = (n : ℝ) := by
  simp [Matrix.trace, Matrix.diag, cosMatrix]

/-- The trace norm (Schatten `1`-norm) of a real symmetric matrix: the sum of the absolute
values of its eigenvalues. -/
noncomputable def traceNorm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- **Trace-norm identity for cosine matrices.**  The Schatten `1`-norm of the cosine matrix
of any family of `n` angles equals `n`. -/
theorem CosTraceNorm3001 (θ : Fin n → ℝ) :
    traceNorm (cosMatrix_isHermitian θ) = (n : ℝ) := by
  have hpsd := cosMatrix_posSemidef θ
  have h : ∀ i, |(cosMatrix_isHermitian θ).eigenvalues i|
      = (cosMatrix_isHermitian θ).eigenvalues i := fun i =>
    abs_of_nonneg (hpsd.eigenvalues_nonneg i)
  have htr : (cosMatrix θ).trace = ∑ i, ((cosMatrix_isHermitian θ).eigenvalues i : ℝ) :=
    (cosMatrix_isHermitian θ).trace_eq_sum_eigenvalues
  simp only [traceNorm, h]
  rw [← htr, cosMatrix_trace]

/-- The trace norm of the cosine matrix is bounded by `n`. -/
theorem cosTraceNorm_le (θ : Fin n → ℝ) :
    traceNorm (cosMatrix_isHermitian θ) ≤ (n : ℝ) :=
  le_of_eq (CosTraceNorm3001 θ)

/-- Each eigenvalue of the cosine matrix lies in `[0, n]`. -/
theorem cosMatrix_eigenvalues_mem_Icc (θ : Fin n → ℝ) (i : Fin n) :
    (cosMatrix_isHermitian θ).eigenvalues i ∈ Set.Icc (0 : ℝ) (n : ℝ) := by
  refine ⟨(cosMatrix_posSemidef θ).eigenvalues_nonneg i, ?_⟩
  have hle : (cosMatrix_isHermitian θ).eigenvalues i
      ≤ ∑ j, |(cosMatrix_isHermitian θ).eigenvalues j| := by
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun j => |(cosMatrix_isHermitian θ).eigenvalues j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hn := CosTraceNorm3001 θ
  rw [traceNorm] at hn
  linarith [hn, hle]

/-- The double cosine sum is a sum of two squares, hence nonnegative. -/
theorem cosSum_eq_sq_add_sq (θ : Fin n → ℝ) :
    ∑ i, ∑ j, Real.cos (θ i - θ j)
      = (∑ i, Real.cos (θ i)) ^ 2 + (∑ i, Real.sin (θ i)) ^ 2 := by
  have : ∀ i : Fin n, ∑ j, Real.cos (θ i - θ j)
      = Real.cos (θ i) * (∑ j, Real.cos (θ j)) + Real.sin (θ i) * (∑ j, Real.sin (θ j)) := by
    intro i
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => Real.cos_sub _ _
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, sq, sq]

/-- Nonnegativity of the double cosine sum. -/
theorem cosSum_nonneg (θ : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, Real.cos (θ i - θ j) := by
  rw [cosSum_eq_sq_add_sq]
  positivity

/-- **Frobenius (Schatten `2`) lower bound.**  Since the cosine matrix has rank at most `2`
and trace `n`, the sum of the squares of its entries is at least `n ^ 2 / 2`. -/
theorem cosFrobeniusSq_ge (θ : Fin n → ℝ) :
    (n : ℝ) ^ 2 / 2 ≤ ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 := by
  have key : 2 * ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2
      = (n : ℝ) ^ 2 + ∑ i, ∑ j, Real.cos (2 * θ i - 2 * θ j) := by
    have expand : ∀ i j : Fin n, 2 * Real.cos (θ i - θ j) ^ 2
        = 1 + Real.cos (2 * θ i - 2 * θ j) := by
      intro i j
      have h : 2 * θ i - 2 * θ j = 2 * (θ i - θ j) := by ring
      rw [h, Real.cos_sq]
      ring
    have hin : ∀ i : Fin n, 2 * ∑ j, Real.cos (θ i - θ j) ^ 2
        = (n : ℝ) + ∑ j, Real.cos (2 * θ i - 2 * θ j) := by
      intro i
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => expand i j), Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sq]
  have hpos := cosSum_nonneg (fun k => 2 * θ k)
  simp only at hpos
  linarith

/-- **Frobenius (Schatten `2`) upper bound.**  All entries of the cosine matrix are bounded
by `1` in absolute value, so the sum of their squares is at most `n ^ 2`. -/
theorem cosFrobeniusSq_le (θ : Fin n → ℝ) :
    ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 ≤ (n : ℝ) ^ 2 := by
  have h : ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have := Real.neg_one_le_cos (θ i - θ j)
    have := Real.cos_le_one (θ i - θ j)
    nlinarith
  simpa [Finset.sum_const, sq] using h

/-- The trace norm of the cosine matrix is bounded by the entrywise `ℓ¹`-norm. -/
theorem cosTraceNorm_le_entrywise (θ : Fin n → ℝ) :
    traceNorm (cosMatrix_isHermitian θ) ≤ ∑ i, ∑ j, |Real.cos (θ i - θ j)| := by
  have hdiag : (n : ℝ) = ∑ i : Fin n, |Real.cos (θ i - θ i)| := by simp
  rw [CosTraceNorm3001 θ, hdiag]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => |Real.cos (θ i - θ j)|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- **Trace norm versus Frobenius norm.**  The square of the trace norm of the cosine matrix is
at most twice the sum of the squares of its entries; this is sharp, reflecting that the matrix
has rank at most `2`. -/
theorem cosTraceNorm_sq_le_two_mul_frobeniusSq (θ : Fin n → ℝ) :
    traceNorm (cosMatrix_isHermitian θ) ^ 2
      ≤ 2 * ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 := by
  have h := cosFrobeniusSq_ge θ
  rw [CosTraceNorm3001 θ]
  linarith

end Brockian

