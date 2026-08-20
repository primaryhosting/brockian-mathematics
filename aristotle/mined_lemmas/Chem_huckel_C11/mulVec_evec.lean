/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma mulVec_evec (k : ZMod 11) :
    C11.mulVec (evec k) = (eps k + eps (-k)) • evec k := by
  funext i
  rw [mulVec_C11]
  have h1 : k * (i + 1) = k * i + k := by ring
  have h2 : k * (i - 1) = k * i + (-k) := by ring
  simp only [evec, Pi.smul_apply, smul_eq_mul, h1, h2, eps_add]
  ring

/-- **Hückel theory for the cycle `C₁₁`.**  The eigenvalues of the adjacency matrix of the
cycle graph on 11 vertices are exactly the numbers `2 cos (2πk/11)`, `k = 0, …, 10`:
each such number is an eigenvalue (with an explicit Fourier eigenvector), and every
eigenvalue is of this form. -/
