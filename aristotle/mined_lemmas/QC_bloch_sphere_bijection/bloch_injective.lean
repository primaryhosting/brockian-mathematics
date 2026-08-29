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

lemma bloch_injective : Function.Injective bloch := by
  intro q₁ q₂ h
  induction q₁ using Quotient.inductionOn with
  | h v =>
    induction q₂ using Quotient.inductionOn with
    | h w =>
      have hv : blochVec v = blochVec w := congrArg Subtype.val h
      obtain ⟨a, b, hab⟩ := v
      obtain ⟨c, d, hcd⟩ := w
      simp only [blochVec] at hv
      have h0 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 0) hv
      have h1 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 1) hv
      have h2 := congrArg (fun p : EuclideanSpace ℝ (Fin 3) => p 2) hv
      simp only at h0 h1 h2
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
      have hre : (a * (starRingEnd ℂ) b).re = (c * (starRingEnd ℂ) d).re := by linarith
      have him : (a * (starRingEnd ℂ) b).im = (c * (starRingEnd ℂ) d).im := by linarith
      have hprod : a * (starRingEnd ℂ) b = c * (starRingEnd ℂ) d := Complex.ext hre him
      obtain ⟨z, hz, hza, hzb⟩ := phase_of_bloch_eq hab hcd hprod h2
      exact Quotient.sound ⟨z, hz, hza, hzb⟩

/-- Every point of `S²` is the Bloch vector of some pure qubit state. -/
