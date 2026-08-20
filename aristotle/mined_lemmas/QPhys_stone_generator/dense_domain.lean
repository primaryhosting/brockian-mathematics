/-
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above is a
-- plain comment and is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Set Topology
open scoped ComplexInnerProductSpace

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Aux


theorem dense_domain (hU : IsUnitaryGroup U) : Dense {x : H | ∃ y, HasGenerator U x y} := by
  have hD : Dense ((domain U : Submodule ℂ H) : Set H) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
      Submodule.eq_bot_iff]
    intro v hv
    have hv' : ∀ u ∈ domain U, ⟪u, v⟫ = 0 := (Submodule.mem_orthogonal _ v).mp hv
    obtain ⟨p, y, hp, hpe⟩ := surjective_add_I hU v
    have hpv : ⟪p, v⟫ = 0 := hv' p ⟨y, hp⟩
    have hsym : ⟪y, p⟫ = ⟪p, y⟫ := hasGenerator_symmetric hU hp hp
    have hvp : ⟪v, p⟫ = 0 := by
      rw [← inner_conj_symm, hpv, map_zero]
    rw [← hpe, inner_add_left, inner_smul_left, Complex.conj_I] at hvp
    have hc : starRingEnd ℂ ⟪y, p⟫ = ⟪y, p⟫ := by rw [inner_conj_symm, hsym]
    have hr : starRingEnd ℂ ⟪p, p⟫ = ⟪p, p⟫ := inner_conj_symm p p
    have hrz : (⟪p, p⟫ : ℂ) = 0 := by
      have h2 : starRingEnd ℂ (⟪y, p⟫ + -Complex.I * ⟪p, p⟫) = 0 := by rw [hvp, map_zero]
      rw [map_add, map_mul, map_neg, hc, hr, Complex.conj_I] at h2
      have h3 : (2 : ℂ) * Complex.I * ⟪p, p⟫ = 0 := by linear_combination h2 - hvp
      simpa [Complex.I_ne_zero] using h3
    have hp0 : p = 0 := inner_self_eq_zero.mp hrz
    have hy0 : y = 0 := by
      rw [hp0] at hp
      exact hasGenerator_unique hp hasGenerator_zero
    rw [← hpe, hp0, hy0, smul_zero, add_zero]
  exact hD

/-- Maximality: the adjoint of the generator is the generator itself. -/
