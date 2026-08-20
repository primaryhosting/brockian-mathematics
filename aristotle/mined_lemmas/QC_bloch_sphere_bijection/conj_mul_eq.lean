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


lemma conj_mul_eq {v w : Qubit} (h : blochRaw v = blochRaw w) :
    (starRingEnd ℂ) v.a * v.b = (starRingEnd ℂ) w.a * w.b := by
  have hx : 2 * (v.a.re * v.b.re + v.a.im * v.b.im)
      = 2 * (w.a.re * w.b.re + w.a.im * w.b.im) := congrArg Sphere2.x h
  have hy : 2 * (v.a.re * v.b.im - v.a.im * v.b.re)
      = 2 * (w.a.re * w.b.im - w.a.im * w.b.re) := congrArg Sphere2.y h
  apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] <;> linarith

