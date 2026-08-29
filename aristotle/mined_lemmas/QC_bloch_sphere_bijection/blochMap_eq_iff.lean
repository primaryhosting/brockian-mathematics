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

/-! ## Pure qubit states -/

/-- A pure state of a single qubit: a unit vector `a|0⟩ + b|1⟩` in `ℂ²`. -/
structure Qubit where
  /-- amplitude of `|0⟩` -/
  a : ℂ
  /-- amplitude of `|1⟩` -/
  b : ℂ
  /-- normalization -/
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

namespace Qubit

/-- Two qubit states are physically identical when they differ by a global phase. -/

theorem blochMap_eq_iff (v w : Qubit) :
    blochMap v = blochMap w ↔ blochX v = blochX w ∧ blochY v = blochY w ∧ blochZ v = blochZ w := by
  constructor
  · intro h
    have h' : (!₂[blochX v, blochY v, blochZ v] : EuclideanSpace ℝ (Fin 3))
        = !₂[blochX w, blochY w, blochZ w] := congrArg Subtype.val h
    refine ⟨?_, ?_, ?_⟩
    · simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) h'
    · simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) h'
    · simpa using congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 2) h'
  · rintro ⟨h1, h2, h3⟩
    simp [blochMap, h1, h2, h3]

