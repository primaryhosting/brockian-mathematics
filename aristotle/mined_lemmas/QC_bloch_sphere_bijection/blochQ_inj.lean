import Mathlib

/-!
# The Bloch sphere

Pure states of a qubit are unit vectors `(a, b) ∈ ℂ²`.  Two such vectors describe the same
physical state when they differ by a *global phase*, i.e. by multiplication with a complex
number of modulus one.  This file shows that the set of pure qubit states modulo global phase
is in bijection with the points of the 2-sphere `S² ⊆ ℝ³`, via the *Bloch map*

`(a, b) ↦ (2 Re (a * conj b), 2 Im (a * conj b), |a|² - |b|²)`.
-/

namespace QC

open Complex ComplexConjugate

/-- A pure qubit state: a unit vector `(a, b)` in `ℂ²`. -/
structure Qubit where
  a : ℂ
  b : ℂ
  unit : normSq a + normSq b = 1

/-- Two pure qubit states are physically equal when they differ by a global phase. -/

lemma blochQ_inj {q r : Qubit} (h : blochQ q = blochQ r) : PhaseRel q r := by
  have h' := congrArg Subtype.val h
  simp only [blochQ, blochVec, Prod.ext_iff] at h'
  have h1 : q.a * conj q.b = r.a * conj r.b := by
    apply Complex.ext <;> linarith [h'.1, h'.2.1]
  have h2 : normSq q.a - normSq q.b = normSq r.a - normSq r.b := h'.2.2
  have hqa : normSq q.a = normSq r.a := by linarith [q.unit, r.unit, h2]
  have hqb : normSq q.b = normSq r.b := by linarith [q.unit, r.unit, h2]
  by_cases hz : q.a = 0
  · have hra : r.a = 0 := by
      have hz' : normSq r.a = 0 := by rw [← hqa, hz]; simp
      exact Complex.normSq_eq_zero.mp hz'
    have hb0 : q.b ≠ 0 := by
      intro hb
      have hu := q.unit
      rw [hz, hb] at hu
      simp at hu
    refine ⟨r.b / q.b, ?_, ?_, ?_⟩
    · rw [Complex.normSq_div, hqb]
      have hnz : normSq r.b ≠ 0 := by rw [← hqb]; simpa using hb0
      field_simp
    · rw [hra, hz]; ring
    · field_simp
  · refine ⟨r.a / q.a, ?_, ?_, ?_⟩
    · rw [Complex.normSq_div, hqa]
      have hnz : normSq r.a ≠ 0 := by rw [← hqa]; simpa using hz
      field_simp
    · field_simp
    · have key : r.a * q.b = q.a * r.b := by
        have hc : conj q.a * q.b = conj r.a * r.b := by
          have hcg := congrArg (starRingEnd ℂ) h1
          simpa [map_mul, mul_comm] using hcg
        have e2 : r.a * conj r.a = (normSq r.a : ℂ) := by rw [Complex.mul_conj]
        have e3 : q.a * conj q.a = (normSq q.a : ℂ) := by rw [Complex.mul_conj]
        have hqa' : ((normSq q.a : ℝ) : ℂ) = ((normSq r.a : ℝ) : ℂ) := by rw [hqa]
        have hane : conj q.a ≠ 0 := by simpa using hz
        have hcancel : conj q.a * (r.a * q.b) = conj q.a * (q.a * r.b) := by
          calc conj q.a * (r.a * q.b) = r.a * (conj q.a * q.b) := by ring
            _ = r.a * (conj r.a * r.b) := by rw [hc]
            _ = (r.a * conj r.a) * r.b := by ring
            _ = ((normSq r.a : ℝ) : ℂ) * r.b := by rw [e2]
            _ = ((normSq q.a : ℝ) : ℂ) * r.b := by rw [hqa']
            _ = (q.a * conj q.a) * r.b := by rw [e3]
            _ = conj q.a * (q.a * r.b) := by ring
        exact mul_left_cancel₀ hane hcancel
      field_simp
      linear_combination -key

/-- Every point of the 2-sphere is the Bloch vector of some pure qubit state. -/
