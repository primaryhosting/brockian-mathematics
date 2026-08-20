import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian

open Matrix

/-- The planar rotation matrix by angle `θ`. -/

lemma abs_diag_le_one_of_orthogonal {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (h : Aᵀ * A = 1) (i : n) : |A i i| ≤ 1 := by
  have hcol : ∑ j, A j i * A j i = 1 := by
    have := congrArg (fun M => M i i) h
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have hle : A i i * A i i ≤ ∑ j, A j i * A j i :=
    Finset.single_le_sum (f := fun j => A j i * A j i)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  rw [hcol] at hle
  exact abs_le_one_iff_mul_self_le_one.mpr hle

/-- Trace-norm bound: for a real orthogonal matrix all singular values are `1`, so the
trace norm equals the dimension and `|tr A| ≤ card n`. -/
