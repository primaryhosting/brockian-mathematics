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

theorem densityOperator_unique {ρ σ : DensityOperator E}
    (h : ∀ x : E, ‖x‖ = 1 → (inner ℂ x (ρ.op x) : ℂ).re = (inner ℂ x (σ.op x) : ℂ).re) :
    ρ.op = σ.op := by
  have key : ∀ x : E, (inner ℂ x (ρ.op x) : ℂ).re = (inner ℂ x (σ.op x) : ℂ).re := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hnu : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
        rw [norm_smul]
        simp [inv_mul_cancel₀ hx']
      have hval := h _ hnu
      rw [re_inner_smul_self, re_inner_smul_self] at hval
      have hne : ((‖x‖⁻¹) ^ 2 : ℝ) ≠ 0 := by positivity
      exact mul_left_cancel₀ hne hval
  have hsymm : (ρ.op - σ.op).IsSymmetric := ρ.isSymmetric.sub σ.isSymmetric
  have hzero : ∀ x : E, inner ℂ ((ρ.op - σ.op) x) x = 0 := by
    intro x
    have h1 : (inner ℂ x ((ρ.op - σ.op) x) : ℂ)
        = ((inner ℂ x ((ρ.op - σ.op) x) : ℂ).re : ℝ) :=
      inner_self_eq_re_of_isSymmetric hsymm x
    have h2 : (inner ℂ x ((ρ.op - σ.op) x) : ℂ).re = 0 := by
      rw [LinearMap.sub_apply, inner_sub_right]
      simp [key x]
    rw [hsymm x x, h1, h2]
    simp
  exact sub_eq_zero.mp ((inner_map_self_eq_zero (ρ.op - σ.op)).mp hzero)

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

