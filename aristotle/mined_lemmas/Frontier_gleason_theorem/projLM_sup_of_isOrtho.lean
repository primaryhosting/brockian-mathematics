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

lemma projLM_sup_of_isOrtho [FiniteDimensional ℂ E] {U V : Submodule ℂ E} (h : U ⟂ V) :
    projLM (U ⊔ V) = projLM U + projLM V := by
  ext x
  show (U ⊔ V).starProjection x = U.starProjection x + V.starProjection x
  refine eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.add_mem_sup (starProjection_apply_mem U x) (starProjection_apply_mem V x)) ?_
  intro w hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
  have hxu : ⟪x - U.starProjection x, u⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).1 (sub_starProjection_mem_orthogonal x) u hu
  have hxv : ⟪x - V.starProjection x, v⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal' _ _).1 (sub_starProjection_mem_orthogonal x) v hv
  have hPv : ⟪U.starProjection x, v⟫_ℂ = 0 :=
    (Submodule.isOrtho_iff_inner_eq.1 h) _ (starProjection_apply_mem U x) v hv
  have hQu : ⟪V.starProjection x, u⟫_ℂ = 0 := by
    have h1 : ⟪u, V.starProjection x⟫_ℂ = 0 :=
      (Submodule.isOrtho_iff_inner_eq.1 h) u hu _ (starProjection_apply_mem V x)
    rw [← inner_conj_symm, h1, map_zero]
  simp only [inner_add_right, inner_sub_left, inner_add_left] at *
  linear_combination hxu + hxv - hPv - hQu

/-- The Born-rule assignment `U ↦ tr (ρ P_U)` attached to an operator `ρ`. -/
