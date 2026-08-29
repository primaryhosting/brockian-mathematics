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


theorem trace_comp_starProjection (A : H →ₗ[ℂ] H) (S : Submodule ℂ H) :
    LinearMap.trace ℂ H (A ∘ₗ (S.starProjection : H →L[ℂ] H).toLinearMap)
      = ∑ i, ⟪((stdOrthonormalBasis ℂ S i : S) : H), A ((stdOrthonormalBasis ℂ S i : S) : H)⟫_ℂ := by
  have h1 : (S.starProjection : H →L[ℂ] H).toLinearMap
      = S.subtype ∘ₗ (S.orthogonalProjection : H →L[ℂ] S).toLinearMap := rfl
  rw [h1, ← LinearMap.comp_assoc,
    LinearMap.trace_comp_comm' ((S.orthogonalProjection : H →L[ℂ] S).toLinearMap)
      (A ∘ₗ S.subtype),
    LinearMap.trace_eq_sum_inner _ (stdOrthonormalBasis ℂ S)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Submodule.inner_orthogonalProjection_eq_of_mem_left _ _

/-- Finite additivity of a quantum measure along a finite orthonormal family. -/
