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


def GleasonFrameCore : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E],
    3 ≤ Module.finrank ℂ E → GleasonFrameProperty E

/-- **Gleason's theorem** (reduction to the frame-function core).

Let `H` be a complex Hilbert space of dimension at least three, and let `μ` be a quantum
measure on `H`, i.e. a nonnegative, normalized, orthogonally additive function on the lattice
of subspaces of `H`.  Granting the analytic core of Gleason's theorem (`GleasonFrameCore`:
nonnegative frame functions in dimension at least three are quadratic forms), there is a
density operator `T` on `H` — a positive operator of unit trace — such that

`μ K = tr (T ∘ P_K)`

for every subspace `K`, where `P_K` is the orthogonal projection onto `K`.  In other words,
every quantum measure comes from a density operator. -/
