import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix SimpleGraph Finset

/-- The adjacency matrix of the cycle graph `C₁₃` (the Hückel matrix of the
`C₁₃` carbon ring, in units where `α = 0` and `β = 1`). -/

lemma vec_ne_zero (k : Fin 13) : vec k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [vec] at h0

/-- The (unnormalized) discrete Fourier matrix, whose columns are the eigenvectors. -/
