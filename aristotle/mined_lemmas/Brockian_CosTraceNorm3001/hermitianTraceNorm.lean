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

noncomputable def hermitianTraceNorm {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The trace of a real symmetric matrix is the sum of its eigenvalues. -/
