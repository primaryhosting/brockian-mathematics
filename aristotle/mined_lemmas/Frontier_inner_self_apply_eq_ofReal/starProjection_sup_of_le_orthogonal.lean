/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace BigOperators

namespace Frontier

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

/-- A *density operator* on a complex Hilbert space: a self-adjoint, positive semidefinite
operator of unit trace. -/
structure IsDensityOperator (ρ : H →ₗ[ℂ] H) : Prop where
  isSymmetric : ρ.IsSymmetric
  nonneg : ∀ v : H, 0 ≤ (⟪v, ρ v⟫_ℂ).re
  trace_one : ρ.trace ℂ H = 1

/-- A *quantum measure* (a state on the lattice of closed subspaces): a nonnegative, normalized,
orthogonally additive function on subspaces. -/
structure QuantumMeasure (μ : Submodule ℂ H → ℝ) : Prop where
  nonneg : ∀ S, 0 ≤ μ S
  top : μ ⊤ = 1
  additive : ∀ S T : Submodule ℂ H, S ≤ Tᗮ → μ (S ⊔ T) = μ S + μ T

/-- The quantum measure induced by a density operator `ρ`: `S ↦ tr (ρ ∘ P_S)`, where `P_S` is
the orthogonal projection onto `S`. -/

lemma starProjection_sup_of_le_orthogonal {S T : Submodule ℂ H} (h : S ≤ Tᗮ) :
    ((S ⊔ T).starProjection : H →L[ℂ] H) = S.starProjection + T.starProjection := by
  ext x
  simp only [ContinuousLinearMap.add_apply]
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ ?_
  · exact add_mem (Submodule.mem_sup_left (Submodule.starProjection_apply_mem S x))
      (Submodule.mem_sup_right (Submodule.starProjection_apply_mem T x))
  · intro w hw
    rcases Submodule.mem_sup.mp hw with ⟨a, ha, c, hc, rfl⟩
    have hSa : ⟪x - S.starProjection x, a⟫_ℂ = 0 :=
      inner_eq_zero_symm.mp ((Submodule.sub_starProjection_mem_orthogonal x) a ha)
    have hTc : ⟪x - T.starProjection x, c⟫_ℂ = 0 :=
      inner_eq_zero_symm.mp ((Submodule.sub_starProjection_mem_orthogonal x) c hc)
    have hTa : ⟪T.starProjection x, a⟫_ℂ = 0 :=
      (Submodule.isOrtho_iff_le.mpr h).symm.inner_eq (Submodule.starProjection_apply_mem T x) ha
    have hSc : ⟪S.starProjection x, c⟫_ℂ = 0 :=
      (Submodule.isOrtho_iff_le.mpr h).inner_eq (Submodule.starProjection_apply_mem S x) hc
    simp only [inner_sub_left, inner_add_left, inner_add_right] at *
    linear_combination hSa + hTc - hTa - hSc

/-- A density operator induces a quantum measure. -/
