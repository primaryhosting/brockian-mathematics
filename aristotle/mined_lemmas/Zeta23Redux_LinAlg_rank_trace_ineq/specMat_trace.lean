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

lemma specMat_trace (hA : A.IsHermitian) (f : Fin d → ℝ) :
    (specMat hA f).trace = ((∑ i, f i : ℝ) : ℂ) := by
  unfold specMat
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_mul_uni hA, Matrix.one_mul,
    Matrix.trace_diagonal]
  push_cast
  rfl

