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

lemma trace_comp_starProjection_eq_sum {ρ : H →ₗ[ℂ] H} {S : Submodule ℂ H} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) :
    (ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap).trace ℂ H
      = ∑ i, ⟪(b i : H), ρ (b i : H)⟫_ℂ := by
  have h1 : (ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)
      = ∑ i, (InnerProductSpace.rankOne ℂ (ρ (b i : H)) (b i : H) : H →L[ℂ] H).toLinearMap := by
    rw [b.starProjection_eq_sum_rankOne]
    ext z
    simp [Finset.sum_apply, map_sum]
  rw [h1, map_sum]
  exact Finset.sum_congr rfl fun i _ => InnerProductSpace.trace_rankOne _ _

/-- `traceMeasure ρ S` is the sum of the diagonal values of the quadratic form of `ρ` over an
orthonormal basis of `S`. -/
