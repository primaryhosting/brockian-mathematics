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

/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`, recorded as a pair of amplitudes
`(a, b)` with `|a|² + |b|² = 1`. -/

theorem bloch_phase_invariant {p q : PureState} (h : PhaseRel p q) : bloch p = bloch q := by
  obtain ⟨z, hz, ha, hb⟩ := h
  have hzz : normSq z = 1 := by
    rw [Complex.normSq_eq_norm_sq, hz]; norm_num
  have h0 : ((starRingEnd ℂ) q.a * q.b) = ((starRingEnd ℂ) p.a * p.b) := by
    rw [ha, hb, map_mul]
    have : (starRingEnd ℂ) z * z = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, hzz]; norm_num
    calc (starRingEnd ℂ) z * (starRingEnd ℂ) p.a * (z * p.b)
        = ((starRingEnd ℂ) z * z) * ((starRingEnd ℂ) p.a * p.b) := by ring
      _ = (starRingEnd ℂ) p.a * p.b := by rw [this, one_mul]
  have h1 : normSq q.a = normSq p.a := by rw [ha, map_mul, hzz, one_mul]
  have h2 : normSq q.b = normSq p.b := by rw [hb, map_mul, hzz, one_mul]
  simp only [bloch, blochVec, h0, h1, h2]

/-- The Bloch map descends to the quotient by global phase. -/
