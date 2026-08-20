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

lemma blochVec_mem_S2 (v : Qubit) : blochVec v.val ∈ S2 := by
  obtain ⟨⟨a, b⟩, h⟩ := v
  rw [mem_S2_iff]
  simp only [blochVec_zero, blochVec_one, blochVec_two]
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im] at *
  linear_combination (a.re * a.re + a.im * a.im + b.re * b.re + b.im * b.im + 1) * h

/-- The Bloch vector is invariant under a global phase. -/
