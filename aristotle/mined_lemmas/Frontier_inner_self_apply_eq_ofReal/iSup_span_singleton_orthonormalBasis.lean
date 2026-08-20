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

lemma iSup_span_singleton_orthonormalBasis {S : Submodule ℂ H} {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ S) :
    (⨆ i ∈ (Finset.univ : Finset ι), Submodule.span ℂ {(b i : H)}) = S := by
  have h0 : (⨆ i ∈ (Finset.univ : Finset ι), Submodule.span ℂ {(b i : H)})
      = Submodule.span ℂ (Set.range fun i => (b i : H)) := by
    simp [Submodule.span_range_eq_iSup]
  rw [h0]
  have h1 : Submodule.span ℂ (Set.range fun i => (b i : S)) = ⊤ := b.toBasis.span_eq
  have h2 := congrArg (Submodule.map S.subtype) h1
  rwa [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h2

omit [FiniteDimensional ℂ H] in
/-- The image in `H` of an orthonormal basis of a subspace is an orthonormal family. -/
