/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem fourierVec_ne_zero (k : ℕ) : fourierVec k ≠ 0 := by
  intro h
  have h0 : fourierVec k 0 = 0 := by rw [h]; rfl
  rw [fourierVec] at h0
  simp at h0

/-- `ζ^k + ζ^(-k)` is an eigenvalue of the adjacency matrix, with eigenvector `fourierVec k`. -/
