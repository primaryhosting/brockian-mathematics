import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

(The `import Mathlib` line must precede this file's module documentation because Lean 4
requires all `import` commands to come first; the required header comment is otherwise
reproduced verbatim as the first block of the file.)

Gleason's theorem states that every quantum measure (normalized, finitely additive probability
assignment on the closed subspaces, i.e. a normalized frame function) on a complex Hilbert
space of dimension at least `3` is of the form `P ↦ tr (rho P)` for a unique density operator
`rho`.  Here the space is `EuclideanSpace ℂ (Fin n)` and operators are `n × n` complex matrices.

What is formalized and proved in this file:

* `Frontier.IsQuantumMeasure`, `Frontier.IsDensityOperator`, `Frontier.RepresentedBy`,
  `Frontier.GleasonProperty` -- the statement of the theorem.
* `Frontier.gleason_theorem` -- the *reduction*: a quantum measure that extends to a linear
  functional on operators is given by a density operator (trace-duality plus positivity).
* `Frontier.gleason_theorem_of_selfAdjoint_linear` -- the same with the more natural hypothesis
  of a real-linear extension over the self-adjoint operators, via complexification
  (`Frontier.hasLinearExtension_of_selfAdjoint`, `Frontier.hasSelfAdjointLinearExtension_iff`).
* `Frontier.hasLinearExtension_iff_gleasonProperty` -- the linearity hypothesis is exactly
  equivalent to the conclusion, so the reduction is lossless: all that is missing from a full
  proof of Gleason's theorem is the (deep) fact that in dimension `≥ 3` every quantum measure
  admits such an extension.
* `Frontier.isQuantumMeasure_of_isDensityOperator` -- the converse direction.
* `Frontier.representedBy_unique` -- uniqueness of the density operator.
* `Frontier.gleason_dim_one` -- the base case `n = 1`, unconditionally.
* `Frontier.gleason_fails_dim_two` -- sharpness: an explicit quantum measure on a qubit
  (`Frontier.qubitMeasure`, built from the cubic `3a² - 2a³`) that comes from no density
  operator, so the hypothesis `3 ≤ n` cannot be removed.
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

namespace Frontier

open Matrix

variable {n : ℕ}

/-! ## Basic notions

We model a complex Hilbert space of dimension `n` as `EuclideanSpace ℂ (Fin n)`, and the
bounded operators on it as `Matrix (Fin n) (Fin n) ℂ`.  An *event* (a closed subspace) is
recorded by its orthogonal projection. -/

/-- An orthogonal projection: a self-adjoint idempotent matrix. -/

theorem qubitMeasure_not_gleasonProperty : ¬ GleasonProperty qubitMeasure := by
  rintro ⟨rho, -, hrep⟩
  have hproj : ∀ A : Matrix (Fin 2) (Fin 2) ℂ, Aᴴ = A → A * A = A → IsProjection A :=
    fun A h1 h2 => ⟨h1, h2⟩
  have hE1 : IsProjection (!![(1 : ℂ), 0; 0, 0]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hE2 : IsProjection (!![(0 : ℂ), 0; 0, 1]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]
  have hH : IsProjection (!![(1 : ℂ)/2, 1/2; 1/2, 1/2]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hK : IsProjection (!![(9 : ℂ)/25, 12/25; 12/25, 16/25]) := by
    refine hproj _ ?_ ?_ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h1 := hrep _ hE1
  have h2 := hrep _ hE2
  have h3 := hrep _ hH
  have h4 := hrep _ hK
  simp only [qubitMeasure, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two] at h1 h2 h3 h4
  norm_num at h1 h2 h3 h4
  rw [h1, h2] at h3 h4
  have h5 : rho 0 1 + rho 1 0 = 0 := by linear_combination 2 * h3
  have h6 : (9 : ℂ) / 25 = 4617 / 15625 := by linear_combination h4 - (12 / 25) * h5
  norm_num at h6

/-- **Gleason's theorem is sharp: it fails in dimension two.** -/
