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

lemma span_singleton_le_orthogonal_iSup {ι : Type*} [DecidableEq ι] {v : ι → H}
    (hv : Orthonormal ℂ v) (s : Finset ι) {a : ι} (ha : a ∉ s) :
    Submodule.span ℂ {v a} ≤ (⨆ i ∈ s, Submodule.span ℂ {v i})ᗮ := by
  rw [← Submodule.isOrtho_iff_le, Submodule.isOrtho_iSup_right]
  intro i
  rw [Submodule.isOrtho_iSup_right]
  intro hi
  rw [Submodule.isOrtho_span]
  rintro u hu w hw
  simp only [Set.mem_singleton_iff] at hu hw
  subst hu; subst hw
  exact hv.2 (fun h => ha (h ▸ hi))

omit [FiniteDimensional ℂ H] in
/-- An orthonormal basis of a subspace `S` spans `S`. -/
