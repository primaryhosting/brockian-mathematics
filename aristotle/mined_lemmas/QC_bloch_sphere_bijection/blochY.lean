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

noncomputable def blochY (v : Qubit) : ℝ := 2 * ((starRingEnd ℂ) v.a * v.b).im

/-- Third Bloch coordinate `⟨ψ|σ_z|ψ⟩`. -/
