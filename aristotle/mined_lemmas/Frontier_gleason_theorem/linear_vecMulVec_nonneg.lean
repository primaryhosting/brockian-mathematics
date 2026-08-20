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

lemma linear_vecMulVec_nonneg {φ : Matrix n n ℂ →ₗ[ℂ] ℂ}
    (hpos : ∀ P : Matrix n n ℂ, IsProjection P → 0 ≤ φ P) (v : n → ℂ) :
    0 ≤ φ (Matrix.vecMulVec v (star v)) := by
  rcases eq_or_ne v 0 with rfl | hv
  · have : Matrix.vecMulVec (0 : n → ℂ) (star (0 : n → ℂ)) = 0 := by
      ext a b; simp
    rw [this, map_zero]
  · set c : ℝ := ∑ i, Complex.normSq (v i) with hc
    have hcpos : 0 < c := by
      rcases Function.ne_iff.mp hv with ⟨i, hi⟩
      refine Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      simpa using hi
    have hcne : ((c : ℂ)) ≠ 0 := by simpa using hcpos.ne'
    have h := hpos _ (isProjection_vecMulVec hv)
    rw [map_smul, smul_eq_mul] at h
    have hmul : (0 : ℂ) ≤ (c : ℂ) * ((c : ℂ)⁻¹ * φ (Matrix.vecMulVec v (star v))) :=
      mul_nonneg (by simpa using hcpos.le) h
    rwa [← mul_assoc, mul_inv_cancel₀ hcne, one_mul] at hmul

