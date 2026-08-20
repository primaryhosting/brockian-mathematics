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

lemma sesqOfBilin_hermitian (hs : ∀ x y, B x y = B y x)
    (hI : ∀ x y : H, B (Complex.I • x) (Complex.I • y) = B x y) (x y : H) :
    sesqOfBilin B y x = (starRingEnd ℂ) (sesqOfBilin B x y) := by
  have h1 : B y x = B x y := hs _ _
  have h2 : B y (Complex.I • x) = - B x (Complex.I • y) := by
    rw [hs y (Complex.I • x)]
    exact bilin_smul_I_left hI x y
  simp only [sesqOfBilin, h1, h2]
  apply Complex.ext <;> simp

omit [FiniteDimensional ℂ H] in
