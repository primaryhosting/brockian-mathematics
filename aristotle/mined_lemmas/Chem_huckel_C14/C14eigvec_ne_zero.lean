/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Polynomial SimpleGraph

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₁₄`. -/

lemma C14eigvec_ne_zero (k : Fin 14) : C14eigvec k ≠ 0 := by
  intro hzero
  have h := congrFun hzero 0
  simp [C14eigvec] at h

/-- **Hückel theory for the C₁₄ annulene ring.**
The adjacency (Hückel) matrix of the cycle graph `C₁₄` has eigenvalues `2 cos (2πk/14)`,
`k = 0, …, 13`:
* the explicit vector `j ↦ exp(2πi·jk/14)` is a nonzero eigenvector with
  eigenvalue `2 cos (2πk/14)`;
* the characteristic polynomial factors as `∏ k, (X - 2 cos (2πk/14))`, so these are the
  eigenvalues with multiplicity;
* the spectrum is exactly the set of these 14 numbers. -/
