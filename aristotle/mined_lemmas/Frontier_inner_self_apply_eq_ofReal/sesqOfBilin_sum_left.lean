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

lemma sesqOfBilin_sum_left (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → H) (y : H) :
    sesqOfBilin B (∑ i ∈ s, c i • w i) y
      = ∑ i ∈ s, (starRingEnd ℂ) (c i) * sesqOfBilin B (w i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sesqOfBilin_zero_left]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, sesqOfBilin_add_left, sesqOfBilin_smul_left hI, ih,
        Finset.sum_insert ha]

/-- A phase-invariant symmetric real bilinear form is represented by a complex linear operator. -/
