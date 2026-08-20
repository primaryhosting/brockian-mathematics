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

lemma specMat_eigenvalues (hA : A.IsHermitian) : specMat hA hA.eigenvalues = A := by
  conv_rhs => rw [hA.spectral_theorem]
  unfold specMat
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  rfl

end Spec

/-! ### Traces of products of positive semidefinite matrices -/

