import Mathlib

/-!
# Cos Trace Norm 4001
Category: Brockian Corpus
Target: Brockian.CosTraceNorm4001
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Unfolding of the unitary conjugation star-algebra automorphism used by the matrix
spectral theorem. -/

noncomputable def hermCos {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
      diagonal (fun i => ((Real.cos (hA.eigenvalues i) : ℝ) : ℂ)) *
    star (hA.eigenvectorUnitary : Matrix n n ℂ)

/-- `hermCos hA` is again Hermitian. -/
