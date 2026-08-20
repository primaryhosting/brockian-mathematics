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

lemma rot_orthogonal (θ : ℝ) : (rot θ)ᵀ * rot θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The trace of the rotation matrix is `2 cos θ`. -/
