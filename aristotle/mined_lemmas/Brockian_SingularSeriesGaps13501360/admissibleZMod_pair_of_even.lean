import Mathlib

/-!
# Singular Series Gaps 13501360 — `ZMod`/Mathlib formulation

Companion to `RequestProject/SingularSeriesGaps13501360.lean`.  The target file there is stated
with elementary `Int` arithmetic (it must begin with a fixed header comment, which precludes an
`import` line); here the same mathematics is recorded in the idiomatic Mathlib language of
`Finset ℤ` and `ZMod p`.
-/

namespace Brockian

/-- A finite set of integers misses a residue class modulo `p`. -/

theorem admissibleZMod_pair_of_even {h : ℤ} (hh : Even h) : AdmissibleZMod {0, h} := by
  intro p hp
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨1, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hval : ((h : ℤ) : ZMod 2) = 0 := by
      obtain ⟨k, hk⟩ := hh
      have : ((h : ℤ) : ZMod 2) = (k : ZMod 2) + (k : ZMod 2) := by
        rw [hk]; push_cast; ring
      rw [this]
      have : (k : ZMod 2) + (k : ZMod 2) = 2 * (k : ZMod 2) := by ring
      rw [this]
      simp [show (2 : ZMod 2) = 0 from rfl]
    rcases hx with rfl | rfl
    · simp
    · rw [hval]; decide
  · refine admissibleAtZMod_of_card_lt hp.pos ?_
    have hcard : ({0, h} : Finset ℤ).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have h2 := hp.two_le
    omega

