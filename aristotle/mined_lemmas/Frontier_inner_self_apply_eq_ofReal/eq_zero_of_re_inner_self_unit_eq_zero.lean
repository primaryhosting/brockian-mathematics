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

lemma eq_zero_of_re_inner_self_unit_eq_zero {τ : H →ₗ[ℂ] H} (hs : τ.IsSymmetric)
    (h : ∀ v : H, ‖v‖ = 1 → (⟪v, τ v⟫_ℂ).re = 0) : τ = 0 := by
  have h1 : ∀ w : H, 0 ≤ (⟪w, τ w⟫_ℂ).re :=
    nonneg_of_nonneg_on_unit fun v hv => (h v hv).ge
  have h2 : ∀ w : H, 0 ≤ (⟪w, (-τ) w⟫_ℂ).re := by
    refine nonneg_of_nonneg_on_unit fun v hv => ?_
    simp [h v hv]
  have h3 : ∀ w : H, ⟪w, τ w⟫_ℂ = 0 := by
    intro w
    have hw2 := h2 w
    simp only [LinearMap.neg_apply, inner_neg_right, Complex.neg_re, neg_nonneg] at hw2
    have : (⟪w, τ w⟫_ℂ).re = 0 := le_antisymm hw2 (h1 w)
    rw [inner_self_apply_eq_ofReal hs w, this]
    simp
  refine (hs.inner_map_self_eq_zero).mp fun x => ?_
  rw [← inner_conj_symm, h3 x, map_zero]

end Auxiliary

section QuantumMeasureLemmas

variable {μ : Submodule ℂ H → ℝ}

omit [FiniteDimensional ℂ H] in
