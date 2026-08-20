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

lemma QuantumMeasure.sum_span_singleton (hμ : QuantumMeasure μ) {ι : Type*} [DecidableEq ι]
    {v : ι → H} (hv : Orthonormal ℂ v) (s : Finset ι) :
    μ (⨆ i ∈ s, Submodule.span ℂ {v i}) = ∑ i ∈ s, μ (Submodule.span ℂ {v i}) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hμ.bot
  | insert a s ha ih =>
      rw [Finset.iSup_insert, hμ.additive _ _ (span_singleton_le_orthogonal_iSup hv s ha),
        Finset.sum_insert ha, ih]

end QuantumMeasureLemmas

section TraceMeasureLemmas

/-- The trace of `ρ ∘ P_S`, computed in an orthonormal basis of `S`. -/
