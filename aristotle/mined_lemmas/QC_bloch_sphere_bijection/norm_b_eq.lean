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


lemma norm_b_eq {v w : Qubit} (h : blochRaw v = blochRaw w) : ‖v.b‖ = ‖w.b‖ := by
  have hz : (v.a.re ^ 2 + v.a.im ^ 2) - (v.b.re ^ 2 + v.b.im ^ 2)
      = (w.a.re ^ 2 + w.a.im ^ 2) - (w.b.re ^ 2 + w.b.im ^ 2) := congrArg Sphere2.z h
  have hv := v.components
  have hw := w.components
  have : ‖v.b‖ ^ 2 = ‖w.b‖ ^ 2 := by
    rw [sq_norm_complex, sq_norm_complex]; linarith
  have h1 : (0:ℝ) ≤ ‖v.b‖ := norm_nonneg _
  have h2 : (0:ℝ) ≤ ‖w.b‖ := norm_nonneg _
  nlinarith

