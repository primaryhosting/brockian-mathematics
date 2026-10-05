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

lemma C13_mulVec_vec (k : Fin 13) : C13 *ᵥ vec k = eval13 k • vec k := by
  funext j
  have h : (C13 *ᵥ vec k) j = ∑ l, C13 j l * vec k l := rfl
  rw [h, sum_adj, vec_pred, vec_succ, Pi.smul_apply, smul_eq_mul,
    ← zeta_pow_twelve_add k]
  ring

