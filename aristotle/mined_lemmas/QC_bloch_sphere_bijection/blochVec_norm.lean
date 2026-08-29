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

import Mathlib
/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex

namespace QC

/-- A pure state of a qubit: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are equivalent when they differ by a global phase. -/

lemma blochVec_norm (v : Qubit) : ‖blochVec v‖ = 1 := by
  obtain ⟨a, b, h⟩ := v
  rw [blochVec, EuclideanSpace.norm_eq, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  rw [show (1:ℝ) = Real.sqrt 1 by simp]
  congr 1
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  nlinarith [h, sq_nonneg (a.re * b.re), sq_nonneg (a.im * b.im)]

