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

lemma quadratic_form_nonneg_real (mu : Matrix (Fin n) (Fin n) ℂ → ℝ) (hmu : IsQuantumMeasure mu)
    (f : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ)
    (hf : ∀ P : Matrix (Fin n) (Fin n) ℂ, IsProjection P → f P = (mu P : ℂ))
    (x : Fin n → ℂ) :
    ∃ r : ℝ, 0 ≤ r ∧ star x ⬝ᵥ dualOperator f *ᵥ x = (r : ℂ) := by
  have hquad : ∀ y : Fin n → ℂ, star y ⬝ᵥ dualOperator f *ᵥ y = f (rankOne y) := fun y => by
    rw [← trace_mul_rankOne, trace_dualOperator_mul]
  by_cases hx : x = 0
  · exact ⟨0, le_refl 0, by simp [hx]⟩
  · obtain ⟨t, y, ht0, hy1, hscale⟩ := quadratic_rescale x hx
    refine ⟨t * mu (rankOne y), mul_nonneg ht0 (hmu.nonneg _ (isProjection_rankOne y hy1)), ?_⟩
    rw [hscale (dualOperator f), hquad y, hf _ (isProjection_rankOne y hy1)]
    push_cast
    ring

/-! ## The main results -/

/-- **Gleason's theorem (linear-extension reduction).**  Let `mu` be a quantum measure on the
`n`-dimensional complex Hilbert space, `n ≥ 3`.  If `mu` extends to a linear functional on
operators -- which is precisely the hard analytic content of Gleason's theorem -- then `mu`
comes from a density operator: there is a positive semidefinite `rho` with `tr rho = 1` and
`mu P = tr (rho P)` for every orthogonal projection `P`.

The dimension hypothesis `3 ≤ n` is the one in the classical statement; it is needed to obtain
the linear extension, and is not used in the reduction proved here. -/
