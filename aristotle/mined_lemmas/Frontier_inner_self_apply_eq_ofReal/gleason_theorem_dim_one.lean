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

theorem gleason_theorem_dim_one (hdim : Module.finrank ℂ H = 1) (μ : Submodule ℂ H → ℝ)
    (hμ : QuantumMeasure μ) :
    ∃ ρ : H →ₗ[ℂ] H, IsDensityOperator ρ ∧ ∀ S : Submodule ℂ H, μ S = traceMeasure ρ S := by
  have hpos : 0 < Module.finrank ℂ H := by omega
  refine ⟨maximallyMixed H, isDensityOperator_maximallyMixed hpos, fun S => ?_⟩
  rcases eq_or_ne S ⊥ with rfl | hS
  · rw [hμ.bot, traceMeasure_bot]
  · have hST : S = ⊤ := by
      have h1 : 0 < Module.finrank ℂ S :=
        Nat.pos_of_ne_zero fun h => hS (Submodule.finrank_eq_zero.mp h)
      have h2 : Module.finrank ℂ S ≤ Module.finrank ℂ H := Submodule.finrank_le S
      exact Submodule.eq_top_of_finrank_eq (by omega)
    rw [hST, hμ.top, (traceMeasure_isQuantumMeasure
      (isDensityOperator_maximallyMixed hpos)).top]

/-- **Gleason's theorem from the weaker (quadratic form) core hypothesis.**  If the frame
function of a quantum measure `μ` is a symmetric real quadratic form, then `μ` comes from a
density operator.  As in `gleason_theorem`, the dimension hypothesis is part of the classical
statement but enters only through the core hypothesis. -/
