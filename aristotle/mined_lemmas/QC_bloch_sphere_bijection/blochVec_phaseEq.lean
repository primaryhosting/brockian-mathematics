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

lemma blochVec_phaseEq {v w : Qubit} (h : PhaseEq v w) : blochVec v = blochVec w := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hnz : normSq z = 1 := by rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have hprod : w.a * (starRingEnd ℂ) w.b = v.a * (starRingEnd ℂ) v.b := by
    rw [ha, hb, map_mul]
    calc z * v.a * ((starRingEnd ℂ) z * (starRingEnd ℂ) v.b)
        = (z * (starRingEnd ℂ) z) * (v.a * (starRingEnd ℂ) v.b) := by ring
      _ = v.a * (starRingEnd ℂ) v.b := by rw [Complex.mul_conj, hnz]; simp
  have hna : normSq w.a = normSq v.a := by rw [ha, map_mul, hnz, one_mul]
  have hnb : normSq w.b = normSq v.b := by rw [hb, map_mul, hnz, one_mul]
  rw [blochVec, blochVec, hprod, hna, hnb]

/-- The Bloch map, from pure qubit states modulo global phase to the unit sphere `S² ⊆ ℝ³`. -/
