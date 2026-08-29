import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Polynomial

/-- Adjacency matrix of the cycle graph `C₃` (the Hückel matrix of cyclopropenyl,
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

lemma C3_eigenvalue_iff (μ : ℝ) :
    (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ C3adj.mulVec v = μ • v) ↔ (μ = 2 ∨ μ = -1) := by
  have key : (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ (C3adj - μ • 1).mulVec v = 0) ↔ (C3adj - μ • 1).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff
  have hre : ∀ v : Fin 3 → ℝ, (C3adj - μ • 1).mulVec v = 0 ↔ C3adj.mulVec v = μ • v := by
    intro v
    rw [Matrix.sub_mulVec, sub_eq_zero, smul_mulVec, Matrix.one_mulVec]
  simp only [hre] at key
  rw [key, Matrix.det_fin_three]
  simp [C3adj]
  constructor
  · intro h
    have h2 : (μ - 2) * (μ + 1) ^ 2 = 0 := by nlinarith [h]
    rcases mul_eq_zero.1 h2 with h1 | h1
    · left; linarith
    · right; nlinarith [sq_nonneg (μ + 1)]
  · rintro (rfl | rfl) <;> ring

/-! ### Complex Bloch (Hückel molecular orbital) eigenvectors -/

/-- The primitive cube root of unity `ω = exp(2πi/3)`. -/
