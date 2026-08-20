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

theorem traceMeasure_isQuantumMeasure {ρ : H →ₗ[ℂ] H} (hρ : IsDensityOperator ρ) :
    QuantumMeasure (traceMeasure ρ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro S
    rw [traceMeasure_eq_sum (stdOrthonormalBasis ℂ S)]
    exact Finset.sum_nonneg fun i _ => hρ.nonneg _
  · rw [traceMeasure, Submodule.starProjection_top]
    simp only [ContinuousLinearMap.coe_id]
    rw [LinearMap.comp_id, hρ.trace_one]
    simp
  · intro S T hST
    rw [traceMeasure, traceMeasure, traceMeasure, starProjection_sup_of_le_orthogonal hST]
    have : (ρ ∘ₗ ((S.starProjection + T.starProjection : H →L[ℂ] H)).toLinearMap)
        = (ρ ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)
          + (ρ ∘ₗ (T.starProjection : H →L[ℂ] H).toLinearMap) := by
      ext z; simp
    rw [this, map_add, Complex.add_re]

@[simp]
