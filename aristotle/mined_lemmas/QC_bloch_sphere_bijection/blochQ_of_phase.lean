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

lemma blochQ_of_phase {q r : Qubit} (h : PhaseRel q r) : blochQ q = blochQ r := by
  obtain ⟨c, hc, ha, hb⟩ := h
  have hmul : r.a * conj r.b = q.a * conj q.b := by
    rw [ha, hb, map_mul]
    have hcc : c * conj c = (normSq c : ℂ) := by rw [Complex.mul_conj]
    calc c * q.a * (conj c * conj q.b) = (c * conj c) * (q.a * conj q.b) := by ring
      _ = q.a * conj q.b := by rw [hcc, hc]; simp
  have hna : normSq r.a = normSq q.a := by rw [ha, Complex.normSq_mul, hc, one_mul]
  have hnb : normSq r.b = normSq q.b := by rw [hb, Complex.normSq_mul, hc, one_mul]
  apply Subtype.ext
  simp only [blochQ, blochVec, hmul, hna, hnb]

/-- The Bloch map, descended to pure states modulo global phase. -/
