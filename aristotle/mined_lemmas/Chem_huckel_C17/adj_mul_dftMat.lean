/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open SimpleGraph Matrix Polynomial Complex

namespace Chem

/-- The primitive 17-th root of unity `exp(2πi/17)`. -/

lemma adj_mul_dftMat :
    (cycleGraph 17).adjMatrix ℂ * dftMat = dftMat * Matrix.diagonal huckelEig := by
  ext j k
  have hL : ((cycleGraph 17).adjMatrix ℂ * dftMat) j k
      = ((cycleGraph 17).adjMatrix ℂ *ᵥ (fun l => dftMat l k)) j := rfl
  rw [hL, adjMatrix_mulVec_cycle17, Matrix.mul_diagonal, dftMat_apply, dftMat_apply,
    dftMat_apply, huckelEig_eq]
  have hsub : (j - 1 : Fin 17) = j + 16 := by
    have : ∀ x : Fin 17, x - 1 = x + 16 := by decide
    exact this j
  rw [hsub]
  have e1 : ((j + 16 : Fin 17) : ℕ) * (k : ℕ) % 17 = ((j : ℕ) * (k : ℕ) + 16 * (k : ℕ)) % 17 := by
    have hv : ((j + 16 : Fin 17) : ℕ) = ((j : ℕ) + 16) % 17 := by
      rw [Fin.val_add]; rfl
    have h1 : ((j : ℕ) + 16) % 17 * (k : ℕ) ≡ ((j : ℕ) + 16) * (k : ℕ) [MOD 17] :=
      Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
    have h2 : ((j : ℕ) + 16) * (k : ℕ) = (j : ℕ) * (k : ℕ) + 16 * (k : ℕ) := by ring
    rw [h2] at h1
    rw [hv]
    exact h1
  have e2 : ((j + 1 : Fin 17) : ℕ) * (k : ℕ) % 17 = ((j : ℕ) * (k : ℕ) + (k : ℕ)) % 17 := by
    have hv : ((j + 1 : Fin 17) : ℕ) = ((j : ℕ) + 1) % 17 := by
      rw [Fin.val_add]; rfl
    have h1 : ((j : ℕ) + 1) % 17 * (k : ℕ) ≡ ((j : ℕ) + 1) * (k : ℕ) [MOD 17] :=
      Nat.ModEq.mul_right _ (Nat.mod_modEq _ _)
    have h2 : ((j : ℕ) + 1) * (k : ℕ) = (j : ℕ) * (k : ℕ) + (k : ℕ) := by ring
    rw [h2] at h1
    rw [hv]
    exact h1
  rw [zeta17_pow_congr e1, zeta17_pow_congr e2, pow_add, pow_add]
  ring

