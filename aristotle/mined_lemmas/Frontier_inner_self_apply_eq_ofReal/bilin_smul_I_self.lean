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

lemma bilin_smul_I_self {μ : Submodule ℂ H → ℝ} (hB : ∀ v : H, ‖v‖ = 1 →
    μ (Submodule.span ℂ {v}) = B v v) (x : H) :
    B (Complex.I • x) (Complex.I • x) = B x x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hrpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    set u : H := (‖x‖⁻¹ : ℝ) • x with hu
    have hnu : ‖u‖ = 1 := norm_smul_inv_norm hx
    have hnIu : ‖Complex.I • u‖ = 1 := by rw [norm_smul, hnu]; simp
    have hspan : Submodule.span ℂ {Complex.I • u} = Submodule.span ℂ {u} :=
      Submodule.span_singleton_smul_eq (IsUnit.mk0 _ Complex.I_ne_zero) _
    have hkey : B (Complex.I • u) (Complex.I • u) = B u u := by
      rw [← hB _ hnIu, ← hB _ hnu, hspan]
    have hxu : x = (‖x‖ : ℝ) • u := by
      rw [hu, smul_smul, mul_inv_cancel₀ hrpos.ne', one_smul]
    calc B (Complex.I • x) (Complex.I • x)
        = B ((‖x‖ : ℝ) • (Complex.I • u)) ((‖x‖ : ℝ) • (Complex.I • u)) := by
          rw [← smul_comm, ← hxu]
      _ = ‖x‖ * (‖x‖ * B (Complex.I • u) (Complex.I • u)) := by simp [map_smul]
      _ = ‖x‖ * (‖x‖ * B u u) := by rw [hkey]
      _ = B x x := by
          conv_rhs => rw [hxu]
          simp [map_smul]

omit [FiniteDimensional ℂ H] in
/-- Phase invariance of the associated bilinear form. -/
