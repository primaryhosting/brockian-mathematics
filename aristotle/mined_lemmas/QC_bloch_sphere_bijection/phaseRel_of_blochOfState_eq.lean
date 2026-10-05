/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is written as a plain block comment rather than a module
-- docstring `/-! ... -/` because Lean 4 requires all `import` commands to come
-- before any command, and a module docstring counts as a command.)
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

set_option grind.warning false

namespace QC

open Complex

/-- A (normalized) pure qubit state vector: a unit vector of `ℂ²`. -/

theorem phaseRel_of_blochOfState_eq {p q : QubitState}
    (h : blochOfState p = blochOfState q) : PhaseRel p q := by
  obtain ⟨⟨a, b⟩, hp⟩ := p
  obtain ⟨⟨c, d⟩, hq⟩ := q
  have h' : blochVec ⟨(a, b), hp⟩ = blochVec ⟨(c, d), hq⟩ := congrArg Subtype.val h
  simp only [blochVec, Prod.mk.injEq] at h'
  obtain ⟨h1, h2, h3⟩ := h'
  simp only at hp hq h1 h2 h3
  have hab : (starRingEnd ℂ) a * b = (starRingEnd ℂ) c * d := by
    apply Complex.ext <;> linarith
  have hna : normSq a = normSq c := by linarith
  have hnb : normSq b = normSq d := by linarith
  by_cases ha : a = 0
  · have hc : c = 0 := by
      have : normSq c = 0 := by rw [← hna, ha]; simp
      exact normSq_eq_zero.mp this
    have hb1 : normSq b = 1 := by rw [ha] at hp; simpa using hp
    have hb0 : b ≠ 0 := by
      intro hb; rw [hb] at hb1; simp at hb1
    refine ⟨d / b, ?_, ?_, ?_⟩
    · rw [map_div₀, ← hnb, hb1]; simp
    · show c = _ * a
      rw [ha, hc, mul_zero]
    · show d = _ * b
      field_simp
  · have hna0 : normSq a ≠ 0 := fun h0 => ha (normSq_eq_zero.mp h0)
    have hconj : (starRingEnd ℂ) a ≠ 0 := by simpa using ha
    have hcb : c * b = a * d := by
      refine mul_left_cancel₀ hconj ?_
      calc (starRingEnd ℂ) a * (c * b) = c * ((starRingEnd ℂ) a * b) := by ring
        _ = c * ((starRingEnd ℂ) c * d) := by rw [hab]
        _ = (c * (starRingEnd ℂ) c) * d := by ring
        _ = ((normSq c : ℝ) : ℂ) * d := by rw [Complex.mul_conj]
        _ = ((normSq a : ℝ) : ℂ) * d := by rw [hna]
        _ = (a * (starRingEnd ℂ) a) * d := by rw [Complex.mul_conj]
        _ = (starRingEnd ℂ) a * (a * d) := by ring
    refine ⟨c / a, ?_, ?_, ?_⟩
    · rw [map_div₀, ← hna]
      field_simp
    · show c = _ * a
      field_simp
    · show d = _ * b
      field_simp
      linear_combination -hcb

