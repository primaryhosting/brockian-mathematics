import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Matrix Polynomial Finset

namespace Chem

/-- A primitive 11th root of unity. -/

lemma dft_mul_inv : dftMatrix * dftMatrixInv = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ l : Fin 11,
      dftMatrix j l * dftMatrixInv l k = (11 : ℂ)⁻¹ * ee (l * (j - k)) := by
    intro l
    simp only [dftMatrix, dftMatrixInv]
    rw [show ee (j * l) * ((11 : ℂ)⁻¹ * ee (-(l * k)))
        = (11 : ℂ)⁻¹ * (ee (j * l) * ee (-(l * k))) by ring, ← ee_add, fin11_ring1]
  rw [Finset.sum_congr rfl fun l _ => hterm l, ← Finset.mul_sum, sum_ee, Matrix.one_apply]
  by_cases hjk : j = k
  · subst hjk; simp
  · rw [if_neg (sub_ne_zero_of_ne hjk), if_neg hjk, mul_zero]

/-- The adjacency matrix of `C₁₁` is diagonalized by the discrete Fourier transform. -/
