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

lemma specMat_mul (hA : A.IsHermitian) (f g : Fin d → ℝ) :
    specMat hA f * specMat hA g = specMat hA (fun i => f i * g i) := by
  unfold specMat
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)ᴴ)
      (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ), star_mul_uni hA, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal]
  congr 2
  funext i
  push_cast
  ring

