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

theorem bloch_injective_mod_phase {p q : PureState} (h : bloch p = bloch q) : PhaseRel p q := by
  have hv : blochVec p = blochVec q := congrArg Subtype.val h
  have e0 : 2 * ((starRingEnd ℂ) p.a * p.b).re = 2 * ((starRingEnd ℂ) q.a * q.b).re := by
    rw [← blochVec_apply_zero, ← blochVec_apply_zero, hv]
  have e1 : 2 * ((starRingEnd ℂ) p.a * p.b).im = 2 * ((starRingEnd ℂ) q.a * q.b).im := by
    rw [← blochVec_apply_one, ← blochVec_apply_one, hv]
  have e2 : normSq p.a - normSq p.b = normSq q.a - normSq q.b := by
    rw [← blochVec_apply_two, ← blochVec_apply_two, hv]
  have hprod : (starRingEnd ℂ) p.a * p.b = (starRingEnd ℂ) q.a * q.b :=
    Complex.ext (by linarith) (by linarith)
  have hp := p.norm_eq
  have hq := q.norm_eq
  have hna : normSq p.a = normSq q.a := by linarith
  have hnb : normSq p.b = normSq q.b := by linarith
  by_cases hpa : p.a = 0
  · have hqa : q.a = 0 := by
      have : normSq q.a = 0 := by rw [← hna, hpa]; simp
      exact normSq_eq_zero.mp this
    have hpb : p.b ≠ 0 := by
      intro h0
      rw [hpa, h0] at hp; simp at hp
    refine ⟨q.b / p.b, ?_, ?_, ?_⟩
    · rw [norm_div, ← norm_eq_of_normSq_eq hnb]
      exact div_self (by simpa using hpb)
    · rw [hpa, hqa, mul_zero]
    · field_simp
  · have hqa : q.a ≠ 0 := by
      intro h0
      rw [h0] at hna; simp at hna; exact hpa hna
    have hcpa : (starRingEnd ℂ) p.a ≠ 0 := by simpa using hpa
    have key : q.a * p.b = p.a * q.b := by
      have h5 : (starRingEnd ℂ) p.a * (q.a * p.b) = (starRingEnd ℂ) p.a * (p.a * q.b) := by
        calc (starRingEnd ℂ) p.a * (q.a * p.b)
            = q.a * ((starRingEnd ℂ) p.a * p.b) := by ring
          _ = q.a * ((starRingEnd ℂ) q.a * q.b) := by rw [hprod]
          _ = ((starRingEnd ℂ) q.a * q.a) * q.b := by ring
          _ = (normSq q.a : ℂ) * q.b := by rw [← Complex.normSq_eq_conj_mul_self]
          _ = (normSq p.a : ℂ) * q.b := by rw [hna]
          _ = ((starRingEnd ℂ) p.a * p.a) * q.b := by rw [← Complex.normSq_eq_conj_mul_self]
          _ = (starRingEnd ℂ) p.a * (p.a * q.b) := by ring
      exact mul_left_cancel₀ hcpa h5
    refine ⟨q.a / p.a, ?_, ?_, ?_⟩
    · rw [norm_div, ← norm_eq_of_normSq_eq hna]
      exact div_self (by simpa using hpa)
    · field_simp
    · field_simp
      linear_combination -key

