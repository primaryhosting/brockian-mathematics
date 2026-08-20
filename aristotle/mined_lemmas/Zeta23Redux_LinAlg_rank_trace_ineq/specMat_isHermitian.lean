import Mathlib

/-!
# Rank Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.rank_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators ComplexOrder

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ}

/-- The real part of the trace of a matrix. -/

lemma specMat_isHermitian (hA : A.IsHermitian) (f : Fin d → ℝ) :
    (specMat hA f).IsHermitian := by
  unfold specMat Matrix.IsHermitian
  have h : (star fun i => ((f i : ℝ) : ℂ)) = fun i => ((f i : ℝ) : ℂ) := by
    funext i; simp
  simp [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.diagonal_conjTranspose, h]

