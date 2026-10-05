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

lemma U_apply (j k : Fin 13) : U j k = (om ^ (j : ℕ)) ^ (k : ℕ) := by
  rw [U, vec, zeta, ← pow_mul, ← pow_mul, Nat.mul_comm]

