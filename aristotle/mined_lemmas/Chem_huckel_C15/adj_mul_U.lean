/-
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat

set_option maxHeartbeats 1000000

namespace Chem

open SimpleGraph Matrix

/-- A primitive 15-th root of unity. -/

lemma adj_mul_U : (cycleGraph 15).adjMatrix ℂ * U = U * D := by
  ext i k
  rw [adjMatrix_mul_apply, U_apply, U_apply, D, Matrix.mul_diagonal, U_apply, ← eig_eq]
  have e1 : zeta ^ (((i - 1 : Fin 15) : ℕ) * (k : ℕ))
      = zeta ^ ((i : ℕ) * (k : ℕ) + 14 * (k : ℕ)) := by
    apply zeta_pow_congr
    rw [fin15_sub_one_val]
    calc ((i : ℕ) + 14) % 15 * (k : ℕ)
        ≡ ((i : ℕ) + 14) * (k : ℕ) [MOD 15] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = (i : ℕ) * (k : ℕ) + 14 * (k : ℕ) := by ring
  have e2 : zeta ^ (((i + 1 : Fin 15) : ℕ) * (k : ℕ))
      = zeta ^ ((i : ℕ) * (k : ℕ) + (k : ℕ)) := by
    apply zeta_pow_congr
    rw [fin15_add_one_val]
    calc ((i : ℕ) + 1) % 15 * (k : ℕ)
        ≡ ((i : ℕ) + 1) * (k : ℕ) [MOD 15] := Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
      _ = (i : ℕ) * (k : ℕ) + (k : ℕ) := by ring
  rw [e1, e2, pow_add, pow_add]
  ring

/-- **Hückel theory for the C₁₅ ring.**  The spectrum (set of eigenvalues) of the adjacency
matrix of the cycle graph `C₁₅` is exactly `{2 cos (2πk/15) : k = 0, …, 14}`. -/
