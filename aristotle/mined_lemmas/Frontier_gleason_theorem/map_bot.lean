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

/-- A *quantum measure* (a finitely additive probability measure on the lattice of closed
subspaces, i.e. on the projection lattice) of a complex Hilbert space `H`.

In finite dimensions every subspace is closed, so we index by `Submodule ℂ H`. -/
structure QuantumMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  /-- The probability assigned to a subspace (equivalently, to its orthogonal projection). -/
  toFun : Submodule ℂ H → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg' : ∀ S, 0 ≤ toFun S
  /-- The whole space has probability one. -/
  total' : toFun ⊤ = 1
  /-- Additivity over orthogonal subspaces. -/
  additive' : ∀ S T : Submodule ℂ H, S ≤ Tᗮ → toFun (S ⊔ T) = toFun S + toFun T

namespace QuantumMeasure

instance : CoeFun (QuantumMeasure H) (fun _ => Submodule ℂ H → ℝ) := ⟨QuantumMeasure.toFun⟩

variable (μ : QuantumMeasure H)


theorem map_bot : μ ⊥ = 0 := by
  have h := μ.additive (S := (⊥ : Submodule ℂ H)) (T := (⊥ : Submodule ℂ H)) bot_le
  simp only [bot_sup_eq] at h
  linarith

end QuantumMeasure

/-- `A` is a density operator: symmetric (self-adjoint), positive semidefinite, of unit trace. -/
structure IsDensityOperator (A : H →ₗ[ℂ] H) : Prop where
  isSymmetric : A.IsSymmetric
  nonneg : ∀ x : H, 0 ≤ (⟪x, A x⟫_ℂ).re
  trace_eq_one : LinearMap.trace ℂ H A = 1

omit [FiniteDimensional ℂ H] in
/-- A singleton spanned by a vector orthogonal to a span is orthogonal to that span. -/
