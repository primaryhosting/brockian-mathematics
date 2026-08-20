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

lemma quadratic_rescale (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ (t : ℝ) (y : Fin n → ℂ), 0 ≤ t ∧ star y ⬝ᵥ y = 1 ∧
      ∀ B : Matrix (Fin n) (Fin n) ℂ, star x ⬝ᵥ B *ᵥ x = (t : ℂ) * (star y ⬝ᵥ B *ᵥ y) := by
  set t : ℝ := ∑ i, ‖x i‖ ^ 2 with ht
  have ht0 : 0 ≤ t := Finset.sum_nonneg fun i _ => by positivity
  have hpos : 0 < t := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => by positivity)
      ⟨i, Finset.mem_univ i, pow_pos (norm_pos_iff.mpr hi) 2⟩
  obtain ⟨s, hspos, hst⟩ : ∃ s : ℝ, 0 < s ∧ t = s * s :=
    ⟨Real.sqrt t, Real.sqrt_pos.mpr hpos, (Real.mul_self_sqrt ht0).symm⟩
  have hsne : s ≠ 0 := ne_of_gt hspos
  set c : ℝ := s⁻¹ with hc
  have hcct : c * c * t = 1 := by
    rw [hc, hst]
    field_simp
  have hctC : (c : ℂ) * (c : ℂ) * (t : ℂ) = 1 := by
    have h := congrArg (fun r : ℝ => (r : ℂ)) hcct
    push_cast at h
    simpa using h
  refine ⟨t, (c : ℂ) • x, ht0, ?_, ?_⟩
  · have h1 : star ((c : ℂ) • x) ⬝ᵥ ((c : ℂ) • x) = ((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ x) := by
      simp only [Pi.star_apply, dotProduct, Pi.smul_apply, smul_eq_mul, Complex.star_def,
        map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h1, dotProduct_star_self, ← ht]
    exact hctC
  · intro B
    have hscale : star ((c : ℂ) • x) ⬝ᵥ B *ᵥ ((c : ℂ) • x)
        = ((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ B *ᵥ x) := by
      simp only [Pi.star_apply, dotProduct, Matrix.mulVec, Pi.smul_apply, smul_eq_mul,
        Complex.star_def, map_mul, Complex.conj_ofReal, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [hscale]
    have h5 : (t : ℂ) * ((c : ℂ) * (c : ℂ)) = 1 := by rw [← hctC]; ring
    calc star x ⬝ᵥ B *ᵥ x
        = ((t : ℂ) * ((c : ℂ) * (c : ℂ))) * (star x ⬝ᵥ B *ᵥ x) := by rw [h5, one_mul]
      _ = (t : ℂ) * (((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ B *ᵥ x)) := by ring

/-- If a quantum measure `mu` is the restriction of a linear functional `f`, then the quadratic
form of the dual operator of `f` takes nonnegative real values. -/
