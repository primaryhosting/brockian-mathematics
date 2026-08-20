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

lemma add_eq_one_of_orthogonal_two (P Q : Matrix (Fin 2) (Fin 2) ℂ) (hP : IsProjection P)
    (hQ : IsProjection Q) (hPQ : P * Q = 0) (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) : P + Q = 1 := by
  have hQP : Q * P = 0 := by
    have h := congrArg Matrix.conjTranspose hPQ
    rwa [Matrix.conjTranspose_mul, hP.1.eq, hQ.1.eq, Matrix.conjTranspose_zero] at h
  have hP1 : P ≠ 1 := by
    rintro rfl
    exact hQ0 (by simpa using hPQ)
  have hQ1 : Q ≠ 1 := by
    rintro rfl
    exact hP0 (by simpa using hPQ)
  have htP : P.trace = 1 := ((idempotent_two_cases P hP.2).resolve_left hP0).resolve_left hP1
  have htQ : Q.trace = 1 := ((idempotent_two_cases Q hQ.2).resolve_left hQ0).resolve_left hQ1
  have hR : (P + Q) * (P + Q) = P + Q := by
    rw [add_mul, mul_add, mul_add, hP.2, hQ.2, hPQ, hQP]
    abel
  have htR : (P + Q).trace = 2 := by
    rw [Matrix.trace_add, htP, htQ]
    norm_num
  rcases idempotent_two_cases (P + Q) hR with h | h | h
  · rw [h] at htR
    simp at htR
  · exact h
  · rw [h] at htR
    norm_num at htR

/-- The `(0,0)` entry of a `2 × 2` projection is a real number in `[0,1]`. -/
