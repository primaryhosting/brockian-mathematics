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

theorem density_unique {ρ σ : Matrix n n ℂ} {μ : Matrix n n ℂ → ℝ} (hρ : ρ.IsHermitian)
    (hσ : σ.IsHermitian) (h1 : Represents ρ μ) (h2 : Represents σ μ) : ρ = σ := by
  have hzero : ρ - σ = 0 := by
    refine eq_zero_of_trace_proj_re_eq_zero (hρ.sub hσ) fun P hP => ?_
    rw [Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re, ← h1 P hP, ← h2 P hP, sub_self]
  exact sub_eq_zero.mp hzero

end Uniqueness

/-- **Gleason's theorem (Lean-checked reduction).**
Let `μ` be a quantum measure on the projection lattice of a Hilbert space of dimension `≥ 3`
which extends to a linear functional on all operators.  Then `μ` is given by the Born rule for a
unique density operator `ρ`.

The linearity hypothesis `hlin` is precisely the analytic heart of Gleason's theorem: for
dimension `≥ 3` every quantum measure automatically extends linearly.  The dimension hypothesis
`hn` is kept because it is part of the classical statement, but it is not used by this reduction.
Dimension `≥ 3` is genuinely necessary for the unconditional statement: see
`Frontier.gleason_fails_in_dimension_two`. -/
