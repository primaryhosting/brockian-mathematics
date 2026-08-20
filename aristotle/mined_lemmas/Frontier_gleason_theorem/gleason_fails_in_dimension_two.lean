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

theorem gleason_fails_in_dimension_two :
    ∃ μ : Matrix (Fin 2) (Fin 2) ℂ → ℝ, QuantumMeasure μ ∧
      ∀ ρ : Matrix (Fin 2) (Fin 2) ℂ, ¬ Represents ρ μ := by
  refine ⟨badMeasure, badMeasure_quantumMeasure, fun ρ hrep => ?_⟩
  have h00 := hrep _ isProjection_e00
  have h11 := hrep _ isProjection_e11
  have hu := hrep _ isProjection_projU
  have hv := hrep _ isProjection_projV
  have v00 : badMeasure e00 = 1 := by norm_num [badMeasure, e00]
  have v11 : badMeasure e11 = 0 := by norm_num [badMeasure, e11]
  have vu : badMeasure projU = 49 / 125 := by norm_num [badMeasure, projU]
  have vv : badMeasure projV = 49 / 125 := by norm_num [badMeasure, projV]
  have tr00 : (ρ * e00).trace = ρ 0 0 := by
    rw [Matrix.trace_fin_two]
    simp [e00, Matrix.mul_apply, Fin.sum_univ_two]
  have tr11 : (ρ * e11).trace = ρ 1 1 := by
    rw [Matrix.trace_fin_two]
    simp [e11, Matrix.mul_apply, Fin.sum_univ_two]
  have hsum : (ρ * projU).trace + (ρ * projV).trace
      = ((2 / 5 : ℝ) : ℂ) * ρ 0 0 + ((8 / 5 : ℝ) : ℂ) * ρ 1 1 := by
    rw [Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp [projU, projV, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [v00, tr00] at h00
  rw [v11, tr11] at h11
  rw [vu] at hu
  rw [vv] at hv
  have hre : ((ρ * projU).trace + (ρ * projV).trace).re = 2 / 5 := by
    rw [hsum, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← h00, ← h11]
    norm_num
  rw [Complex.add_re, ← hu, ← hv] at hre
  norm_num at hre

end DimTwo

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

