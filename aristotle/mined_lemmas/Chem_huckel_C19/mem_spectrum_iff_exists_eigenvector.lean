import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma mem_spectrum_iff_exists_eigenvector (A : Matrix (Fin 19) (Fin 19) ℂ) (μ : ℂ) :
    μ ∈ spectrum ℂ A ↔ ∃ v : Fin 19 → ℂ, v ≠ 0 ∧ A *ᵥ v = μ • v := by
  have key : ∀ v : Fin 19 → ℂ,
      (algebraMap ℂ (Matrix (Fin 19) (Fin 19) ℂ) μ - A) *ᵥ v = μ • v - A *ᵥ v := by
    intro v
    simp [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, (sub_eq_zero.mp (key v ▸ h)).symm⟩
  · rintro ⟨v, hv, h⟩
    exact ⟨v, hv, by rw [key v, h, sub_self]⟩

/-- **Hückel spectrum of C₁₉.** The spectrum of the adjacency (Hückel) matrix of the
cycle graph `C₁₉` is exactly `{2 cos (2πk/19) : k = 0, …, 18}`. -/
