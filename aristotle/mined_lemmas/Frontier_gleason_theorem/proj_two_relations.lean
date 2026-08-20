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

lemma proj_two_relations {P : Matrix (Fin 2) (Fin 2) ℂ} (hP : IsProjection P) :
    P 0 0 = (((P 0 0).re : ℝ) : ℂ) ∧ P 1 1 = (((P 1 1).re : ℝ) : ℂ) ∧
      P 1 0 = star (P 0 1) ∧
      (P 0 0).re ^ 2 + Complex.normSq (P 0 1) = (P 0 0).re ∧
      P 0 1 * (P 0 0 + P 1 1 - 1) = 0 := by
  obtain ⟨hherm, hidem⟩ := hP
  have h00 : (starRingEnd ℂ) (P 0 0) = P 0 0 := by
    have := congrFun (congrFun hherm 0) 0
    simpa [Matrix.conjTranspose_apply] using this
  have h11 : (starRingEnd ℂ) (P 1 1) = P 1 1 := by
    have := congrFun (congrFun hherm 1) 1
    simpa [Matrix.conjTranspose_apply] using this
  have h10 : (starRingEnd ℂ) (P 0 1) = P 1 0 := by
    have := congrFun (congrFun hherm 1) 0
    simpa [Matrix.conjTranspose_apply] using this
  have e00 : P 0 0 * P 0 0 + P 0 1 * P 1 0 = P 0 0 := by
    have := congrFun (congrFun hidem 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e01 : P 0 0 * P 0 1 + P 0 1 * P 1 1 = P 0 1 := by
    have := congrFun (congrFun hidem 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hre00 : P 0 0 = (((P 0 0).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp h00).symm
  have hre11 : P 1 1 = (((P 1 1).re : ℝ) : ℂ) := (Complex.conj_eq_iff_re.mp h11).symm
  refine ⟨hre00, hre11, h10.symm, ?_, by linear_combination e01⟩
  have hc : ((((P 0 0).re ^ 2 + Complex.normSq (P 0 1) : ℝ)) : ℂ) = (((P 0 0).re : ℝ) : ℂ) := by
    push_cast
    rw [← Complex.mul_conj, ← hre00, h10]
    linear_combination e00
  exact_mod_cast hc

/-- For two orthogonal projections in dimension two, either one of them has vanishing `(0,0)`
entry, or the two entries sum to one. -/
