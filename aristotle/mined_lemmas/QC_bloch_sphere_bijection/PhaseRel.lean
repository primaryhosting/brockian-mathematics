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

def PhaseRel (q r : Qubit) : Prop :=
  ∃ c : ℂ, normSq c = 1 ∧ r.a = c * q.a ∧ r.b = c * q.b

instance phaseSetoid : Setoid Qubit where
  r := PhaseRel
  iseqv :=
    { refl := fun q => ⟨1, by simp, by simp, by simp⟩
      symm := by
        rintro q r ⟨c, hc, ha, hb⟩
        have hc0 : c ≠ 0 := by
          intro h; rw [h] at hc; simp at hc
        refine ⟨c⁻¹, ?_, ?_, ?_⟩
        · rw [Complex.normSq_inv, hc]; norm_num
        · rw [ha]; field_simp
        · rw [hb]; field_simp
      trans := by
        rintro q r s ⟨c, hc, ha, hb⟩ ⟨d, hd, ha', hb'⟩
        exact ⟨d * c, by rw [Complex.normSq_mul, hc, hd]; ring,
          by rw [ha', ha]; ring, by rw [hb', hb]; ring⟩ }

/-- Pure qubit states modulo global phase. -/
