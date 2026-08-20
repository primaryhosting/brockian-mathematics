import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

namespace QC

/-- A pure qubit state: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

/-- A point of the 2-sphere `S² ⊆ ℝ³`. -/
@[ext]
structure Sphere2 where
  x : ℝ
  y : ℝ
  z : ℝ
  norm_eq : x ^ 2 + y ^ 2 + z ^ 2 = 1


def PhaseEq (v w : Qubit) : Prop :=
  ∃ c : ℂ, ‖c‖ = 1 ∧ w.a = c * v.a ∧ w.b = c * v.b

