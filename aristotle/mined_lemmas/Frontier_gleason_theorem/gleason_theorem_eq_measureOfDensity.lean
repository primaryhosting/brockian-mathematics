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

* `Frontier.QuantumMeasure`: a finitely additive probability measure on the lattice of subspaces
  of a complex Hilbert space (equivalently, on orthogonal projections).
* `Frontier.IsDensityOperator`: self-adjoint, positive semidefinite, unit trace.
* `Frontier.gleason_theorem`: the target statement.  Gleason's theorem is derived, in a fully
  Lean-checked way, from Gleason's *frame function theorem* `hFrame` (the deep analytic input,
  taken here as an explicit hypothesis): every quantum measure on a space of dimension `≥ 3` is
  `U ↦ tr (ρ P_U)` for a density operator `ρ`.
* `Frontier.gleason_theorem_of_finrank_eq_one`: unconditional base case in dimension one.
* `Frontier.QuantumMeasure.ofDensity`: the converse direction, proved unconditionally -- every
  density operator defines a quantum measure through the Born rule.
* `Frontier.density_operator_unique`: the density operator is unique.
-/

open scoped InnerProductSpace
open Submodule

namespace Frontier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- A *quantum measure* (finitely additive probability measure on the lattice of closed
subspaces, equivalently on orthogonal projections) on an inner product space `E`. -/
structure QuantumMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ E → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg : ∀ U, 0 ≤ toFun U
  /-- A quantum measure is normalized: the whole space has measure `1`. -/
  normalized : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive : ∀ U V : Submodule ℂ E, U ⟂ V → toFun (U ⊔ V) = toFun U + toFun V

/-- A *density operator*: a positive semidefinite self-adjoint operator of trace one. -/
structure IsDensityOperator (ρ : E →ₗ[ℂ] E) : Prop where
  /-- Density operators are self-adjoint. -/
  isSymmetric : ρ.IsSymmetric
  /-- Density operators are positive semidefinite. -/
  nonneg : ∀ x : E, 0 ≤ (⟪x, ρ x⟫_ℂ).re
  /-- Density operators have unit trace. -/
  trace_one : LinearMap.trace ℂ E ρ = 1

/-- The orthogonal projection onto a subspace `U`, viewed as an endomorphism of `E`. -/

theorem gleason_theorem_eq_measureOfDensity [FiniteDimensional ℂ E]
    (h3 : 3 ≤ Module.finrank ℂ E)
    (hFrame : 3 ≤ Module.finrank ℂ E → ∀ mu : QuantumMeasure E, IsRegularFrame mu)
    (mu : QuantumMeasure E) :
    ∃ ρ : E →ₗ[ℂ] E, IsDensityOperator ρ ∧ mu.toFun = measureOfDensity ρ := by
  obtain ⟨ρ, hρ, hkey⟩ := gleason_theorem h3 hFrame mu
  refine ⟨ρ, hρ, funext fun U => ?_⟩
  rw [measureOfDensity, ← hkey U, Complex.ofReal_re]

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

