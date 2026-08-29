import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Real Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₄` (the Hückel matrix of cyclobutadiene,
with `α = 0`, `β = 1`): vertices are `Fin 4` arranged in a cycle, and `i ~ j` iff
`j = i + 1` or `i = j + 1` (addition modulo `4`). -/

theorem eigen_iff_det (μ : ℝ) :
    (∃ v : Fin 4 → ℝ, v ≠ 0 ∧ C4adj *ᵥ v = μ • v) ↔ μ ^ 4 - 4 * μ ^ 2 = 0 := by
  rw [← det_C4adj_sub μ, ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hve⟩
    exact ⟨v, hv, by simp [Matrix.sub_mulVec, Matrix.smul_mulVec, hve]⟩
  · rintro ⟨v, hv, hvz⟩
    refine ⟨v, hv, ?_⟩
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hvz

/-- The four Hückel eigenvalues, as a set of real numbers. -/
