import Mathlib

/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

universe u

namespace Frontier

open scoped InnerProductSpace

/-- A *quantum measure* (a finitely additive probability measure on the lattice of subspaces of
a Hilbert space): a nonnegative function on subspaces, normalized at the whole space, and
additive on pairs of mutually orthogonal subspaces. -/
structure QuantumMeasure (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The measure of a subspace. -/
  toFun : Submodule ℂ H → ℝ
  /-- A quantum measure is nonnegative. -/
  nonneg' : ∀ K, 0 ≤ toFun K
  /-- A quantum measure is a probability measure. -/
  normalized' : toFun ⊤ = 1
  /-- A quantum measure is additive on orthogonal subspaces. -/
  additive' : ∀ K L : Submodule ℂ H, K ≤ Lᗮ → toFun (K ⊔ L) = toFun K + toFun L

namespace QuantumMeasure

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

instance : CoeFun (QuantumMeasure H) (fun _ => Submodule ℂ H → ℝ) := ⟨QuantumMeasure.toFun⟩


def GleasonFrameProperty (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] : Prop :=
  ∀ μ : QuantumMeasure H, ∃ T : H →ₗ[ℂ] H, T.IsPositive ∧
    ∀ x : H, ‖x‖ = 1 → (μ (Submodule.span ℂ {x}) : ℂ) = ⟪x, T x⟫_ℂ

/-- The analytic core of Gleason's theorem: on every complex Hilbert space of dimension at
least three, every nonnegative frame function (equivalently, the restriction of a quantum
measure to the one-dimensional subspaces) is a quadratic form `x ↦ ⟪x, T x⟫` for some positive
operator `T`.  This is the hard, geometric part of Gleason's argument; it is taken here as an
explicit hypothesis, and `Frontier.gleason_theorem` reduces the full statement to it. -/
