import Mathlib
/-!
# Cos Trace Norm 3001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm3001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset Matrix

/-- The trace norm (Schatten 1-norm) of a real symmetric matrix: the sum of the absolute
values of its eigenvalues, which for a symmetric matrix coincides with the sum of its
singular values. -/

theorem trace_eq_sum_eigenvalues {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : A.trace = ∑ i, hA.eigenvalues i := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut]
  show ((Unitary.toUnits hA.eigenvectorUnitary : (Matrix (Fin n) (Fin n) ℝ)ˣ) *
      diagonal hA.eigenvalues *
      ((Unitary.toUnits hA.eigenvectorUnitary)⁻¹ : (Matrix (Fin n) (Fin n) ℝ)ˣ)).trace = _
  rw [Matrix.trace_units_conj, Matrix.trace_diagonal]

/-- **Cos Trace Norm 3001.**
For the real diagonal matrix `D = diagonal (fun i => cos (θ i))` of size `n`, the absolute
value of its trace is bounded by its trace norm (the sum of its singular values, which for a
real diagonal matrix is `∑ i, |cos (θ i)|`), and that trace norm is in turn bounded by `n`.

The two steps are closed by `Finset.abs_sum_le_sum_abs` (the triangle inequality for finite
sums) and `Real.abs_cos_le_one`. -/
