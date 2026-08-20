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

theorem isDensityOperator_maximallyMixed (hne : 0 < Module.finrank ℂ H) :
    IsDensityOperator (maximallyMixed H) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    simp [maximallyMixed, inner_smul_left, inner_smul_right]
  · intro v
    have h0 : (0 : ℝ) ≤ (⟪v, v⟫_ℂ).re := inner_self_nonneg (𝕜 := ℂ) (x := v)
    have hc : (0 : ℝ) ≤ ((Module.finrank ℂ H : ℝ)⁻¹) := by positivity
    simp only [maximallyMixed, LinearMap.smul_apply, LinearMap.id_apply, inner_smul_right,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hc h0
  · have hn : (Module.finrank ℂ H : ℂ) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hne.ne'
    rw [maximallyMixed, map_smul, LinearMap.trace_id, smul_eq_mul]
    push_cast
    field_simp

end TraceMeasureLemmas

section QuadraticFrame

/-- A weaker (and more primitive) form of the analytic core of Gleason's theorem: the frame
function `v ↦ μ (ℂ ∙ v)` is the quadratic form of a symmetric ℝ-bilinear form on `H`, regarded
as a real vector space. -/
