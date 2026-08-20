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

lemma badMeasure_quantumMeasure : QuantumMeasure badMeasure where
  nonneg P hP := by
    obtain ⟨-, -, -, hpsq, -⟩ := proj_two_relations hP
    have hnn := Complex.normSq_nonneg (P 0 1)
    have h0 : 0 ≤ (P 0 0).re := by nlinarith
    have h1 : (P 0 0).re ≤ 1 := by nlinarith
    have hfac : 0 ≤ (1 + (2 * (P 0 0).re - 1)) *
        (1 - (2 * (P 0 0).re - 1) + (2 * (P 0 0).re - 1) ^ 2) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg (2 * (P 0 0).re - 1 - 1)])
    simp only [badMeasure]
    nlinarith [hfac]
  additive P Q hP hQ hPQ hQP := by
    have hadd : (P + Q) 0 0 = P 0 0 + Q 0 0 := rfl
    simp only [badMeasure, hadd, Complex.add_re]
    rcases two_orthogonal_diag hP hQ hPQ hQP with h | h | h
    · have hQe : (Q 0 0).re = 1 - (P 0 0).re := by linarith
      rw [hQe]; ring
    · rw [h]; ring
    · rw [h]; ring
  normalized := by
    have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := Matrix.one_apply_eq 0
    simp only [badMeasure, h1]
    norm_num

/-- **Gleason's theorem fails in dimension two.** There is a quantum measure on the projections
of `ℂ²` that is not given by the Born rule for any operator. -/
