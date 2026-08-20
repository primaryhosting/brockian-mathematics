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

theorem admissible_pair_of_even {h : Int} (hh : h % 2 = 0) : Admissible [0, h] := by
  intro p hp
  have hp2 : 2 ≤ p := hp.1
  by_cases hne : p = 2
  · subst hne
    refine ⟨1, by omega, by omega, ?_⟩
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega
  · have hp3 : 3 ≤ (p : Int) := by omega
    have hz : (0 : Int) % (p : Int) = 0 := Int.zero_emod _
    by_cases hc : h % (p : Int) = 1
    · refine ⟨2, by omega, by omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hz]; decide
      · rw [hc]; decide
    · refine ⟨1, by omega, by omega, ?_⟩
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · rw [hz]; decide
      · exact hc

/-- A gap pair `{0, h}` with `h` odd is never admissible: modulo `2` the two entries already
cover both residue classes, so the singular series vanishes. -/
