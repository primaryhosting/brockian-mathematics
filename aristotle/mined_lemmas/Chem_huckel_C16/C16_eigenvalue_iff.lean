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

theorem C16_eigenvalue_iff (mu : ℂ) :
    (∃ v : Fin 16 → ℂ, v ≠ 0 ∧ C16 *ᵥ v = mu • v) ↔ ∃ k : Fin 16, mu = huckelLevel k := by
  have hkey : (∃ v : Fin 16 → ℂ, v ≠ 0 ∧ (Matrix.scalar (Fin 16) mu - C16) *ᵥ v = 0) ↔
      (Matrix.scalar (Fin 16) mu - C16).det = 0 := Matrix.exists_mulVec_eq_zero_iff
  have hdet : (Matrix.scalar (Fin 16) mu - C16).det = ∏ k : Fin 16, (mu - huckelLevel k) := by
    rw [← Matrix.eval_charpoly, C16_charpoly]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨v, hv, hAv⟩
    have h0 : (Matrix.scalar (Fin 16) mu - C16) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, hAv, scalar_mulVec, sub_self]
    have := hkey.mp ⟨v, hv, h0⟩
    rw [hdet] at this
    obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp this
    exact ⟨k, by linear_combination hk⟩
  · rintro ⟨k, rfl⟩
    have : (Matrix.scalar (Fin 16) (huckelLevel k) - C16).det = 0 := by
      rw [hdet]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by ring)
    obtain ⟨v, hv, h0⟩ := hkey.mpr this
    refine ⟨v, hv, ?_⟩
    have h1 : (Matrix.scalar (Fin 16) (huckelLevel k)) *ᵥ v - C16 *ᵥ v = 0 := by
      rw [← Matrix.sub_mulVec]; exact h0
    have h2 := sub_eq_zero.mp h1
    rw [← h2, scalar_mulVec]

/-- **Hückel theory for C₁₆.**  The adjacency (Hückel) matrix of the cycle graph `C₁₆`
has characteristic polynomial `∏_{k=0}^{15} (X - 2 cos (2πk/16))`; equivalently its
eigenvalues are exactly the numbers `2 cos (2πk/16)` for `k = 0, …, 15`. -/
