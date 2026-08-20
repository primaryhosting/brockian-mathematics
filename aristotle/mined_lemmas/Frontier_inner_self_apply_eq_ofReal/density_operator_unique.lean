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

theorem density_operator_unique {ρ σ : H →ₗ[ℂ] H} (hρ : ρ.IsSymmetric) (hσ : σ.IsSymmetric)
    (h : ∀ S : Submodule ℂ H, traceMeasure ρ S = traceMeasure σ S) : ρ = σ := by
  have hzero : ρ - σ = 0 := by
    refine eq_zero_of_re_inner_self_unit_eq_zero (hρ.sub hσ) fun v hv => ?_
    have hv2 := h (Submodule.span ℂ {v})
    rw [traceMeasure_span_singleton ρ hv, traceMeasure_span_singleton σ hv] at hv2
    simp only [LinearMap.sub_apply, inner_sub_right, Complex.sub_re, hv2, sub_self]
  exact sub_eq_zero.mp hzero

/-- Orthogonal projections onto orthogonal subspaces add up to the projection onto their join. -/
