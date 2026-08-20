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

lemma specMat_sub (hA : A.IsHermitian) (f g : Fin d → ℝ) :
    specMat hA f - specMat hA g = specMat hA (fun i => f i - g i) := by
  unfold specMat
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [h]

