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

## Contents

* `Frontier.QuantumMeasure`: a finitely additive probability measure on the lattice of subspaces
  of a complex Hilbert space (equivalently, on orthogonal projections).
* `Frontier.IsDensityOperator`: self-adjoint, positive semidefinite, unit trace.
* `Frontier.gleason_theorem`: the target statement.  Gleason's theorem is derived, in a fully
  Lean-checked way, from Gleason's *frame function theorem* `hFrame` (the deep analytic input,
  taken here as an explicit hypothesis): every quantum measure on a space of dimension `≥ 3` is
  `U ↦ tr (ρ P_U)` for a density operator `ρ`.
* `Frontier.gleason_theorem_of_finrank_eq_one`: unconditional base case in dimension one.
* `Frontier.QuantumMeasure.ofDensity`: the converse direction, proved unconditionally -- every
  density operator defines a quantum measure through the Born rule.
* `Frontier.density_operator_unique`: the density operator is unique.
-/

open scoped InnerProductSpace
open Submodule

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A *quantum measure* (finitely additive probability measure on the lattice of closed
subspaces, equivalently on orthogonal projections) on an inner product space `E`. -/
structure QuantumMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ E → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg : ∀ U, 0 ≤ toFun U
  /-- A quantum measure is normalized: the whole space has measure `1`. -/
  normalized : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive : ∀ U V : Submodule ℂ E, U ⟂ V → toFun (U ⊔ V) = toFun U + toFun V

/-- A *density operator*: a positive semidefinite self-adjoint operator of trace one. -/
structure IsDensityOperator (ρ : E →ₗ[ℂ] E) : Prop where
  /-- Density operators are self-adjoint. -/
  isSymmetric : ρ.IsSymmetric
  /-- Density operators are positive semidefinite. -/
  nonneg : ∀ x : E, 0 ≤ (⟪x, ρ x⟫_ℂ).re
  /-- Density operators have unit trace. -/
  trace_one : LinearMap.trace ℂ E ρ = 1

/-- The orthogonal projection onto a subspace `U`, viewed as an endomorphism of `E`. -/

lemma eq_of_inner_self_eq_on_sphere {ρ σ : E →ₗ[ℂ] E}
    (h : ∀ x : E, ‖x‖ = 1 → ⟪x, ρ x⟫_ℂ = ⟪x, σ x⟫_ℂ) : ρ = σ := by
  have hall : ∀ x : E, ⟪x, ρ x⟫_ℂ = ⟪x, σ x⟫_ℂ := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hxn : (‖x‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hx
      have hu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        simp [inv_mul_cancel₀ hxn]
      have hkey := h _ hu
      simp only [LinearMap.map_smul, inner_smul_left, inner_smul_right,
        Complex.conj_ofReal] at hkey
      field_simp at hkey
      have hne : ((1 / ‖x‖ : ℝ) : ℂ) ^ 2 ≠ 0 := by simp [hxn]
      exact mul_left_cancel₀ hne hkey
  have hzero : ρ - σ = 0 := by
    rw [← inner_map_self_eq_zero]
    intro x
    simp only [LinearMap.sub_apply, inner_sub_left]
    rw [← inner_conj_symm (ρ x) x, ← inner_conj_symm (σ x) x, hall x, sub_self]
  exact sub_eq_zero.1 hzero

/-- Uniqueness in Gleason's theorem: a quantum measure determines its density operator. -/
