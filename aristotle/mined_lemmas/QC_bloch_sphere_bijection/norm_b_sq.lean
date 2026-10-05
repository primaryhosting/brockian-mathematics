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

theorem norm_b_sq (v : Qubit) : ‖v.b‖ ^ 2 = v.b.re ^ 2 + v.b.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

end Qubit

/-- Pure qubit states modulo global phase. -/
abbrev PureState : Type := Quotient Qubit.phaseSetoid

/-- The two-sphere `S² ⊆ ℝ³`. -/
abbrev Sphere2 : Type := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-! ## The Bloch vector -/

/-- First Bloch coordinate `⟨ψ|σₓ|ψ⟩`. -/
