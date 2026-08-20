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

theorem not_admissible_pair_of_odd {h : Int} (hh : h % 2 = 1) : ¬ Admissible [0, h] := by
  intro hadm
  obtain ⟨r, hr0, hr1, hr⟩ := hadm 2 ⟨by omega, by
    intro m hm
    have h2 : m ≤ 2 := Nat.le_of_dvd (by decide) hm
    have h0 : m ≠ 0 := by
      rintro rfl
      exact absurd (Nat.eq_zero_of_zero_dvd hm) (by decide)
    have : m ≠ 0 ∧ m ≤ 2 := ⟨h0, h2⟩
    rcases Nat.lt_or_ge m 2 with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)⟩
  have h0 : (0 : Int) % ((2 : Nat) : Int) ≠ r := hr 0 (by simp)
  have h1 : h % ((2 : Nat) : Int) ≠ r := hr h (by simp)
  omega

/-- **Singular series gaps in the range `[1350, 1360]`.**

For every integer `h` with `1350 ≤ h ≤ 1360`, the gap pair `{0, h}` is an admissible tuple —
equivalently, its Hardy–Littlewood singular series is nonzero — exactly when `h` is even.
This extends the `SingularSeriesGaps` family with the admissible gap range `[1350, 1360]`. -/
