/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Contents

* `Frontier.QuantumMeasure` : a quantum measure (frame function) on a complex Hilbert space.
* `Frontier.DensityOperator` : a positive semidefinite self-adjoint operator of trace one.
* `Frontier.gleason_theorem` : Gleason's theorem in the form of a Lean-checked reduction —
  granting the analytic core (the frame function theorem, valid in dimension `≥ 3`), every
  quantum measure is `x ↦ ⟪x, ρ x⟫` for a genuine density operator `ρ`.
* `Frontier.gleason_theorem_of_constant` : an unconditional base case (measures constant on
  the unit sphere, represented by the maximally mixed state).
* `Frontier.DensityOperator.toQuantumMeasure` : the (easy) converse direction.
* `Frontier.densityOperator_unique` : uniqueness of the representing density operator.

Mathlib does not contain Gleason's theorem.  The main Mathlib inputs used here are
`LinearMap.trace_eq_sum_inner` (trace as a sum over an orthonormal basis),
`stdOrthonormalBasis`, and `inner_map_self_eq_zero` (a complex operator with vanishing
quadratic form is zero).
-/

open scoped BigOperators

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- A **quantum measure** (frame function) on a complex Hilbert space `E`:
a function on the unit sphere which is nonnegative and whose values sum to `1` along every
orthonormal basis.  This is the standard "probability assignment to rank one projections":
the value `toFun x` is the probability assigned to the projection onto `span x`. -/
structure QuantumMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The value of the measure on a unit vector, i.e. on the rank one projection it spans. -/
  toFun : E → ℝ
  /-- Nonnegativity on the unit sphere. -/
  nonneg : ∀ x : E, ‖x‖ = 1 → 0 ≤ toFun x
  /-- The values along any orthonormal basis add up to one. -/
  sum_eq_one : ∀ b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E, ∑ i, toFun (b i) = 1

/-- A **density operator**: a positive semidefinite self-adjoint operator of trace one. -/
structure DensityOperator (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] where
  /-- The underlying operator. -/
  op : E →ₗ[ℂ] E
  /-- Self-adjointness. -/
  isSymmetric : op.IsSymmetric
  /-- Positive semidefiniteness. -/
  nonneg : ∀ x : E, 0 ≤ (inner ℂ x (op x) : ℂ).re
  /-- Normalisation. -/
  trace_one : LinearMap.trace ℂ E op = 1

omit [FiniteDimensional ℂ E] in
/-- For a symmetric operator the quadratic form `⟪x, T x⟫` is real. -/

theorem nonneg_of_nonneg_on_sphere {T : E →ₗ[ℂ] E}
    (h : ∀ x : E, ‖x‖ = 1 → 0 ≤ (inner ℂ x (T x) : ℂ).re) (x : E) :
    0 ≤ (inner ℂ x (T x) : ℂ).re := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    have hnu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
      rw [norm_smul]
      simp [inv_mul_cancel₀ hx']
    have hval := h _ hnu
    rw [re_inner_smul_self] at hval
    have hpos : (0:ℝ) < (‖x‖⁻¹) ^ 2 := by positivity
    nlinarith [hval]

/-- **Gleason's theorem** (Lean-checked reduction).

Let `E` be a complex Hilbert space of dimension at least three and let `μ` be a quantum
measure (frame function) on `E`.  Granting the analytic core of Gleason's theorem — the
*frame function theorem*, which states that every quantum measure on such a space is given
by a symmetric quadratic form (hypothesis `hquad`) — the measure `μ` is represented by a
genuine density operator `ρ`: `μ x = ⟪x, ρ x⟫` for every unit vector `x`.

What is proved here is the passage from a bare symmetric quadratic representation to a
*density operator*: positive semidefiniteness (from nonnegativity of `μ` on the sphere) and
unit trace (from the normalisation of `μ` along an orthonormal basis).

The hypothesis `h3 : 3 ≤ finrank ℂ E` is the dimension restriction of Gleason's theorem: it
is exactly what makes `hquad` true (the statement fails in dimension two), but it is not
used again once `hquad` is available. -/
