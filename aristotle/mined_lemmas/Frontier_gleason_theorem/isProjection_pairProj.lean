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

lemma isProjection_pairProj {i j : n} (hij : i ≠ j) : IsProjection (pairProj i j) := by
  set v : n → ℂ := fun a => if a = i then 1 else if a = j then 1 else 0 with hv
  have hvne : v ≠ 0 := by
    intro h
    have := congrFun h i
    simp [hv] at this
  have hsum : (∑ a : n, Complex.normSq (v a)) = 2 := by
    rw [hv, sum_normSq_pair hij 1 1]
    norm_num
  have hmat : Matrix.vecMulVec v (star v)
      = Matrix.single i i 1 + Matrix.single i j 1 + Matrix.single j i 1 + Matrix.single j j 1 := by
    ext a b
    by_cases hai : a = i <;> by_cases haj : a = j <;> by_cases hbi : b = i <;>
      by_cases hbj : b = j <;>
      simp_all [Matrix.vecMulVec_apply, Matrix.single_apply, eq_comm]
  have := isProjection_vecMulVec hvne
  rwa [hsum, hmat, show (((2 : ℝ) : ℂ)) = (2 : ℂ) by norm_num] at this

