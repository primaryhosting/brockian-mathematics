/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₆` (the Hückel matrix of a
16-membered annulene, with `α = 0`, `β = 1`). -/

lemma C16_mul_dft16 : C16 * dft16 = dft16 * Matrix.diagonal huckelLevel := by
  ext j k
  have hsucc : ∀ j : Fin 16, ((j + 1 : Fin 16) : ℕ) % 16 = ((j : ℕ) + 1) % 16 := by decide
  have hpred : ∀ j : Fin 16, ((j - 1 : Fin 16) : ℕ) % 16 = ((j : ℕ) + 15) % 16 := by decide
  have hentry : ∀ l : Fin 16, dft16 l k = zeta16 ^ ((l : ℕ) * (k : ℕ)) := by
    intro l
    rw [dft16, Matrix.vandermonde_apply, ← pow_mul]
  rw [Matrix.mul_apply, Matrix.mul_apply]
  rw [show ∑ l, C16 j l * dft16 l k = dft16 (j - 1) k + dft16 (j + 1) k from
    C16_row_sum (fun l => dft16 l k) j]
  rw [hentry, hentry]
  have h1 : zeta16 ^ (((j + 1 : Fin 16) : ℕ) * (k : ℕ))
      = zeta16 ^ ((j : ℕ) * (k : ℕ)) * zeta16 ^ (k : ℕ) := by
    rw [← pow_add]
    refine zeta16_pow_congr ?_
    calc ((j + 1 : Fin 16) : ℕ) * (k : ℕ) % 16
        = (((j : ℕ) + 1) * (k : ℕ)) % 16 := by
          rw [Nat.mul_mod, hsucc j, ← Nat.mul_mod]
      _ = ((j : ℕ) * (k : ℕ) + (k : ℕ)) % 16 := by ring_nf
  have h2 : zeta16 ^ (((j - 1 : Fin 16) : ℕ) * (k : ℕ))
      = zeta16 ^ ((j : ℕ) * (k : ℕ)) * (zeta16 ^ (k : ℕ))⁻¹ := by
    have hinv : (zeta16 ^ (k : ℕ))⁻¹ = zeta16 ^ (15 * (k : ℕ)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_add, show (k : ℕ) + 15 * (k : ℕ) = 16 * (k : ℕ) by ring, pow_mul,
        zeta16_pow_sixteen, one_pow]
    rw [hinv, ← pow_add]
    refine zeta16_pow_congr ?_
    calc ((j - 1 : Fin 16) : ℕ) * (k : ℕ) % 16
        = (((j : ℕ) + 15) * (k : ℕ)) % 16 := by
          rw [Nat.mul_mod, hpred j, ← Nat.mul_mod]
      _ = ((j : ℕ) * (k : ℕ) + 15 * (k : ℕ)) % 16 := by ring_nf
  rw [h1, h2]
  rw [Finset.sum_eq_single k (fun b _ hb => by
      rw [Matrix.diagonal_apply_ne _ hb, mul_zero]) (by simp)]
  rw [hentry, Matrix.diagonal_apply_eq, huckelLevel, ← zeta16_pow_add_inv (k : ℕ)]
  ring

