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


theorem trace_eq_of_rank_one {T : H →ₗ[ℂ] H} {u y : H} (hT : ∀ w, T w = ⟪u, w⟫_ℂ • y) :
    LinearMap.trace ℂ H T = ⟪u, y⟫_ℂ := by
  rw [LinearMap.trace_eq_sum_inner T (stdOrthonormalBasis ℂ H)]
  have h : ∀ i, ⟪(stdOrthonormalBasis ℂ H) i, T ((stdOrthonormalBasis ℂ H) i)⟫_ℂ
      = ⟪u, (stdOrthonormalBasis ℂ H) i⟫_ℂ * ⟪(stdOrthonormalBasis ℂ H) i, y⟫_ℂ := by
    intro i
    rw [hT, inner_smul_right]
  rw [Finset.sum_congr rfl fun i _ => h i]
  exact (stdOrthonormalBasis ℂ H).sum_inner_mul_inner u y

omit [FiniteDimensional ℂ H] in
/-- For a density operator `A` the quantity `⟪x, A x⟫` is real. -/
