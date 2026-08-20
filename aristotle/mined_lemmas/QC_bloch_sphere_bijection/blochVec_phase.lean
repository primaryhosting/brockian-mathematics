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

open Complex

/-- A normalized qubit state vector: a unit vector in `ℂ²`. -/

lemma blochVec_phase (a b c : ℂ) (hc : normSq c = 1) : blochVec (c * a, c * b) = blochVec (a, b) := by
  simp only [blochVec, map_mul]
  congr 1
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  ext i
  fin_cases i <;> simp <;>
    first
      | linear_combination (a.re * b.re + a.im * b.im) * hc
      | linear_combination (a.re * b.im - a.im * b.re) * hc
      | linear_combination (a.re * a.re + a.im * a.im - b.re * b.re - b.im * b.im) * hc

/-- The Bloch vector of a normalized qubit state, as a point of `S²`. -/
