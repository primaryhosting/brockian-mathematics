import Mathlib

/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Brockian

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The cosine matrix associated to a family of phases `θ`: its `(i, j)` entry is
`cos (θ i - θ j)`. -/
noncomputable def cosMatrix (θ : n → ℝ) : Matrix n n ℝ := Matrix.of fun i j => Real.cos (θ i - θ j)

omit [Fintype n] [DecidableEq n] in
@[simp] lemma cosMatrix_apply (θ : n → ℝ) (i j : n) :
    cosMatrix θ i j = Real.cos (θ i - θ j) := rfl

/-- The trace norm (Schatten 1-norm) of a real matrix, defined for Hermitian (i.e. symmetric)
matrices as the sum of the absolute values of its eigenvalues, and set to `0` otherwise. -/
noncomputable def hermTraceNorm (A : Matrix n n ℝ) : ℝ :=
  if h : A.IsHermitian then ∑ i, |h.eigenvalues i| else 0

lemma hermTraceNorm_of_isHermitian {A : Matrix n n ℝ} (h : A.IsHermitian) :
    hermTraceNorm A = ∑ i, |h.eigenvalues i| := dif_pos h

/-- For a positive semidefinite matrix the trace norm is just the trace. -/
lemma hermTraceNorm_of_posSemidef {A : Matrix n n ℝ} (h : A.PosSemidef) :
    hermTraceNorm A = A.trace := by
  rw [hermTraceNorm_of_isHermitian h.isHermitian]
  have hval : ∀ i, |h.isHermitian.eigenvalues i| = h.isHermitian.eigenvalues i := fun i =>
    abs_of_nonneg (h.eigenvalues_nonneg i)
  simp only [hval]
  rw [h.isHermitian.trace_eq_sum_eigenvalues (𝕜 := ℝ)]
  simp

omit [Fintype n] [DecidableEq n] in
/-- The cosine matrix is symmetric. -/
lemma cosMatrix_isHermitian (θ : n → ℝ) : (cosMatrix θ).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, ← Real.cos_neg (θ j - θ i)]

omit [DecidableEq n] in
/-- The key quadratic-form identity: `xᵀ C x` is a sum of two squares. -/
lemma cosMatrix_dotProduct_mulVec (θ : n → ℝ) (x : n → ℝ) :
    star x ⬝ᵥ (cosMatrix θ *ᵥ x)
      = (∑ i, x i * Real.cos (θ i)) ^ 2 + (∑ i, x i * Real.sin (θ i)) ^ 2 := by
  simp only [star_trivial, dotProduct, Matrix.mulVec, cosMatrix_apply, sq,
    Finset.sum_mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Real.cos_sub]
  ring

omit [DecidableEq n] in
/-- The cosine matrix is positive semidefinite. -/
lemma cosMatrix_posSemidef (θ : n → ℝ) : (cosMatrix θ).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨cosMatrix_isHermitian θ, fun x => ?_⟩
  rw [cosMatrix_dotProduct_mulVec]
  positivity

omit [DecidableEq n] in
/-- The trace of the cosine matrix is the size of the index set. -/
lemma cosMatrix_trace (θ : n → ℝ) : (cosMatrix θ).trace = Fintype.card n := by
  simp [Matrix.trace, Matrix.diag]

/-- **Cos Trace Norm 3001.** For any family of phases `θ : n → ℝ`, the trace norm of the
cosine matrix `C i j = cos (θ i - θ j)` equals the number of indices. -/
theorem CosTraceNorm3001 (θ : n → ℝ) :
    hermTraceNorm (cosMatrix θ) = Fintype.card n := by
  rw [hermTraceNorm_of_posSemidef (cosMatrix_posSemidef θ), cosMatrix_trace]

/-- Trace-norm bound form: the trace norm of a cosine matrix never exceeds the number of
indices (and, by `CosTraceNorm3001`, this bound is attained). -/
theorem CosTraceNorm3001_le (θ : n → ℝ) :
    hermTraceNorm (cosMatrix θ) ≤ Fintype.card n :=
  le_of_eq (CosTraceNorm3001 θ)

end Brockian

#print axioms Brockian.CosTraceNorm3001
#print axioms Brockian.CosTraceNorm3001_le

