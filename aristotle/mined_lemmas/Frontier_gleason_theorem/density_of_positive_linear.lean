/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4.28's module system forbids a `/-!` module docstring before `import`;
-- the header above is therefore a plain block comment and is repeated below.)

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A *quantum measure* on a finite dimensional complex Hilbert space `ℂⁿ` is a map `μ` from the
orthogonal projections to `ℝ` which is nonnegative, finitely additive on orthogonal pairs, and
normalized (`μ 1 = 1`).  Gleason's theorem says that in dimension at least three every such `μ`
is given by the Born rule `μ P = Tr(ρ P)` for a unique density operator `ρ`.

This file contains:

* `Frontier.QuantumMeasure`, `Frontier.IsDensity`, `Frontier.Represents`: the formalized
  statement ingredients;
* `Frontier.born_rule_quantumMeasure`: every density operator gives a quantum measure;
* `Frontier.density_of_positive_linear`: a linear functional on matrices that is nonnegative
  on projections and normalized is the trace against a density operator;
* `Frontier.density_unique`: the density operator representing a measure is unique;
* `Frontier.gleason_theorem`: the Lean-checked reduction of Gleason's theorem to the linearity
  of the frame function (the analytic heart of the classical proof);
* `Frontier.gleason_fails_in_dimension_two`: an explicit quantum measure on the projections of
  `ℂ²` that is represented by no operator, showing that the dimension hypothesis is necessary.
-/

open Matrix Complex
open scoped ComplexOrder

namespace Frontier

section Defs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- An orthogonal projection: a Hermitian idempotent matrix. -/

theorem density_of_positive_linear (φ : Matrix n n ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P) (hone : φ 1 = 1) :
    ∃ ρ : Matrix n n ℂ, IsDensity ρ ∧ ∀ A, φ A = (ρ * A).trace := by
  refine ⟨toMatrix φ, ⟨?_, ?_⟩, fun A => (trace_toMatrix_mul φ A).symm⟩
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    constructor
    · ext a b
      simpa [toMatrix, Matrix.conjTranspose_apply] using star_linear_single hpos a b
    · intro x
      have key : star x ⬝ᵥ ((toMatrix φ) *ᵥ x) = φ (Matrix.vecMulVec x (star x)) := by
        rw [linear_eq_sum_single φ (Matrix.vecMulVec x (star x))]
        simp only [dotProduct, Matrix.mulVec, toMatrix, Matrix.of_apply, Pi.star_apply,
          Matrix.vecMulVec_apply, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      rw [key]
      exact linear_vecMulVec_nonneg hpos x
  · rw [trace_toMatrix, hone]

end LinearReduction

section Uniqueness

variable {n : Type*} [Fintype n] [DecidableEq n]

