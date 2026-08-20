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

noncomputable def lineBasis {v : H} (hv : ‖v‖ = 1) :
    OrthonormalBasis Unit ℂ (Submodule.span ℂ {v}) :=
  OrthonormalBasis.mk (v := fun _ => (⟨v, Submodule.mem_span_singleton_self v⟩ :
      Submodule.span ℂ {v}))
    (by
      rw [orthonormal_iff_ite]
      rintro ⟨⟩ ⟨⟩
      simp [inner_self_eq_norm_sq_to_K, hv])
    (by
      rintro ⟨w, hw⟩ -
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have h : (⟨c • v, hw⟩ : Submodule.span ℂ {v})
          = c • (⟨v, Submodule.mem_span_singleton_self v⟩ : Submodule.span ℂ {v}) := rfl
      rw [h]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩))

omit [FiniteDimensional ℂ H] in
@[simp]
