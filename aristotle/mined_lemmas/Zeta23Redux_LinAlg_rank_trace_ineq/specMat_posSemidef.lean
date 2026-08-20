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

lemma specMat_posSemidef (hA : A.IsHermitian) {f : Fin d → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (specMat hA f).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => ((f i : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    simpa using Complex.zero_le_real.mpr (hf i)
  exact hd.mul_mul_conjTranspose_same _

