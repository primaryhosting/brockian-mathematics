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

lemma blochQ_surj (p : Sphere2) : ∃ q : Qubit, blochQ q = p := by
  obtain ⟨⟨x, y, z⟩, hp⟩ := p
  simp only at hp
  by_cases hz : z = -1
  · refine ⟨⟨0, 1, by simp⟩, ?_⟩
    have hx : x = 0 ∧ y = 0 := by
      constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
    apply Subtype.ext
    simp [blochQ, blochVec, hx.1, hx.2, hz]
  · have hz1 : (0:ℝ) < 1 + z := by
      rcases lt_trichotomy (1 + z) 0 with h | h | h
      · nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (1 + z)]
      · exact absurd (by linarith : z = -1) hz
      · exact h
    set t : ℝ := Real.sqrt ((1 + z) / 2) with ht
    have ht2 : t ^ 2 = (1 + z) / 2 := Real.sq_sqrt (by linarith)
    have htpos : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have hne : t ≠ 0 := ne_of_gt htpos
    set u : ℝ := x / (2 * t) with hu
    set v : ℝ := -(y / (2 * t)) with hv
    have huv : u ^ 2 + v ^ 2 = (1 - z) / 2 := by
      rw [hu, hv]
      field_simp
      nlinarith [ht2, hp]
    have hnb : normSq ((u : ℂ) + (v : ℂ) * I) = u ^ 2 + v ^ 2 := by
      simp [Complex.normSq_apply]; ring
    have hna : normSq ((t : ℝ) : ℂ) = t ^ 2 := by
      simp [Complex.normSq_apply]; ring
    refine ⟨⟨(t : ℂ), (u : ℂ) + (v : ℂ) * I, ?_⟩, ?_⟩
    · rw [hna, hnb, huv, ht2]; ring
    · apply Subtype.ext
      have hre : ((t : ℂ) * conj ((u : ℂ) + (v : ℂ) * I)).re = t * u := by
        simp [Complex.mul_re]
      have him : ((t : ℂ) * conj ((u : ℂ) + (v : ℂ) * I)).im = -(t * v) := by
        simp [Complex.mul_im]
      simp only [blochQ, blochVec, Prod.mk.injEq, hre, him, hna, hnb, huv, ht2]
      refine ⟨?_, ?_, by ring⟩
      · rw [hu]; field_simp
      · rw [hv]; field_simp

/-- **The Bloch sphere.**  Pure qubit states modulo global phase are in bijection with the
points of the 2-sphere `S²`. -/
