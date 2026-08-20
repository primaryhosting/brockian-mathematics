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

lemma nonneg_of_nonneg_on_unit {ρ : H →ₗ[ℂ] H}
    (hpos : ∀ v : H, ‖v‖ = 1 → 0 ≤ (⟪v, ρ v⟫_ℂ).re) (w : H) : 0 ≤ (⟪w, ρ w⟫_ℂ).re := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have hv : ‖(‖w‖⁻¹ : ℂ) • w‖ = 1 := by simp [norm_smul, inv_mul_cancel₀ hn]
    have h2 := hpos _ hv
    have he : ⟪(‖w‖⁻¹ : ℂ) • w, ρ ((‖w‖⁻¹ : ℂ) • w)⟫_ℂ = ((‖w‖⁻¹ : ℝ) ^ 2 : ℝ) • ⟪w, ρ w⟫_ℂ := by
      simp [map_smul, Complex.conj_ofReal]
      ring
    rw [he] at h2
    simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] at h2
    have hp : 0 < ‖w‖⁻¹ ^ 2 := by positivity
    nlinarith

omit [FiniteDimensional ℂ H] in
/-- Distinct members of an orthonormal family span mutually orthogonal lines. -/
