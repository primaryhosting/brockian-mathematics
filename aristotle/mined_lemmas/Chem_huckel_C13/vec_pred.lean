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

lemma vec_pred (k j : Fin 13) : vec k (j - 1) = zeta k ^ 12 * vec k j := by
  have hval : ((j - 1 : Fin 13) : ℕ) = ((j : ℕ) + 12) % 13 := by
    simp [Fin.sub_def, Nat.add_comm]
  rw [vec, vec, hval, pow_mod13 (zeta_pow13 k), pow_add]
  ring

