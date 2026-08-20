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

lemma exists_operator_of_bilin (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) :
    ∃ ρ : H →ₗ[ℂ] H, ∀ x y : H, ⟪x, ρ y⟫_ℂ = sesqOfBilin B x y := by
  classical
  set e := stdOrthonormalBasis ℂ H with he
  refine ⟨∑ i, LinearMap.smulRight
      ({ toFun := fun y => sesqOfBilin B (e i) y
         map_add' := fun y z => sesqOfBilin_add_right _ _ _
         map_smul' := fun c y => by simpa using sesqOfBilin_smul_right c (e i) y } :
        H →ₗ[ℂ] ℂ) (e i), ?_⟩
  intro x y
  have hxe : x = ∑ i, ⟪e i, x⟫_ℂ • e i := (e.sum_repr' x).symm
  have hrhs : sesqOfBilin B x y
      = ∑ i, (starRingEnd ℂ) (⟪e i, x⟫_ℂ) * sesqOfBilin B (e i) y := by
    conv_lhs => rw [hxe]
    exact sesqOfBilin_sum_left hI _ _ _ y
  rw [hrhs]
  simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.coe_mk,
    AddHom.coe_mk, inner_sum, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_conj_symm (e i) x]
  simp [mul_comm]

/-- **Reduction of Gleason's theorem to the quadratic form property.**  If the frame function of
`μ` is a symmetric real quadratic form, then it is the quadratic form of a self-adjoint complex
operator. -/
