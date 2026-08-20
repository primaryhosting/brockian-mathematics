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

lemma sum_normSq_pair {i j : n} (hij : i ≠ j) (x y : ℂ) :
    ∑ a : n, Complex.normSq (if a = i then x else if a = j then y else 0)
      = Complex.normSq x + Complex.normSq y := by
  have hpt : ∀ a : n, Complex.normSq (if a = i then x else if a = j then y else 0)
      = (if a = i then Complex.normSq x else 0) + (if a = j then Complex.normSq y else 0) := by
    intro a
    by_cases h1 : a = i <;> by_cases h2 : a = j <;> simp_all
  rw [Finset.sum_congr rfl fun a _ => hpt a, Finset.sum_add_distrib]
  simp

/-- The rank one projection onto `e i + e j`. -/
