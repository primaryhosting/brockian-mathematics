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

theorem gleasonFrameProperty_of_quadratic {μ : Submodule ℂ H → ℝ}
    (h : GleasonQuadraticFrameProperty μ) : GleasonFrameProperty μ := by
  obtain ⟨B, hs, hB⟩ := h
  have hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y :=
    bilin_smul_I hs (bilin_smul_I_self hB)
  obtain ⟨ρ, hρ⟩ := exists_operator_of_bilin hI
  refine ⟨ρ, ?_, ?_⟩
  · intro x y
    have h0 : (starRingEnd ℂ) ⟪y, ρ x⟫_ℂ = ⟪ρ x, y⟫_ℂ := inner_conj_symm _ _
    have h1 : ⟪ρ x, y⟫_ℂ = (starRingEnd ℂ) (sesqOfBilin B y x) := by
      rw [← h0, hρ y x]
    rw [h1, sesqOfBilin_hermitian hs hI x y]
    simp [hρ x y]
  · intro v hv
    rw [hρ v v, sesqOfBilin_self hs hI v, Complex.ofReal_re]
    exact hB v hv

end QuadraticFrame

/-- **Gleason's theorem** (reduction to its analytic core).

Let `H` be a complex Hilbert space of dimension at least `3` and let `μ` be a quantum measure on
the lattice of subspaces of `H`.  Granting the analytic core of Gleason's theorem
(`GleasonFrameProperty`: the associated frame function on unit vectors is the quadratic form of a
self-adjoint operator — exactly the step that fails in dimension `2`), the measure `μ` comes from
a density operator: there is a density operator `ρ` with `μ S = tr (ρ P_S)` for every subspace `S`.

The dimension hypothesis `hdim` enters only through the core hypothesis and is therefore not used
in this reduction; it is kept because it is part of the statement of Gleason's theorem. -/
