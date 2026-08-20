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

theorem not_admissibleZMod_pair_of_odd {h : ℤ} (hh : Odd h) : ¬ AdmissibleZMod {0, h} := by
  intro hadm
  obtain ⟨r, hr⟩ := hadm 2 Nat.prime_two
  have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
  have h1 : ((h : ℤ) : ZMod 2) ≠ r := hr h (by simp)
  have hval : ((h : ℤ) : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hh
    have : ((h : ℤ) : ZMod 2) = (k : ZMod 2) + (k : ZMod 2) + 1 := by
      rw [hk]; push_cast; ring
    rw [this]
    have : (k : ZMod 2) + (k : ZMod 2) = 2 * (k : ZMod 2) := by ring
    rw [this]
    simp [show (2 : ZMod 2) = 0 from rfl]
  rw [hval] at h1
  simp only [Int.cast_zero] at h0
  have : r = 0 ∨ r = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) r
  rcases this with rfl | rfl
  · exact h0 rfl
  · exact h1 rfl

/-- Mathlib/`ZMod` version of the target: for `1350 ≤ h ≤ 1360`, the gap pair `{0, h}` is
admissible iff `h` is even. -/
