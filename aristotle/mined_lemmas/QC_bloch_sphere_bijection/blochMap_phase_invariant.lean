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

theorem blochMap_phase_invariant {v w : Qubit} (h : Qubit.PhaseRel v w) :
    blochMap v = blochMap w := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hzz : (starRingEnd ℂ) z * z = 1 := by
    rw [Complex.conj_mul']
    norm_cast
    rw [hz]; norm_num
  rw [blochMap_eq_iff]
  have hxy : (starRingEnd ℂ) w.a * w.b = (starRingEnd ℂ) v.a * v.b := by
    rw [ha, hb, map_mul]
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) v.a * (z * v.b)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) v.a * v.b) := by ring
      _ = (starRingEnd ℂ) v.a * v.b := by rw [hzz, one_mul]
  have hna : ‖w.a‖ = ‖v.a‖ := by rw [ha, norm_mul, hz, one_mul]
  have hnb : ‖w.b‖ = ‖v.b‖ := by rw [hb, norm_mul, hz, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [blochX, blochX, hxy]
  · rw [blochY, blochY, hxy]
  · rw [blochZ, blochZ, hna, hnb]

/-- The Bloch map on states modulo global phase. -/
