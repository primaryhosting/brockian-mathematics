/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem huckel_C18_eigenvector_ne_zero (k : ZMod 18) :
    (fun j : ZMod 18 => wch (j * k)) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [wch] at h0

/-- **Hückel theory for C₁₈.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₈` factors as `∏_{k=0}^{17} (X - 2 cos (2πk/18))`; that is, the adjacency
eigenvalues of `C₁₈` are exactly `2 cos (2πk/18)` for `k = 0, …, 17`. -/
