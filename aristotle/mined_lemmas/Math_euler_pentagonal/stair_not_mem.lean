/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma stair_not_mem (h0 : 0 ∉ S) (hne : S.Nonempty) : mx S - stair S ∉ S := by
  rcases eq_or_lt_of_le (stair_le_mx (S := S)) with h | h
  · simpa [h] using h0
  · intro hmem
    have hgt := Nat.findGreatest_is_greatest (P := fun j => Finset.Icc (mx S + 1 - j) (mx S) ⊆ S)
      (k := stair S + 1) (n := mx S) (by simp [stair]) h
    apply hgt
    intro x hx
    simp only [Finset.mem_Icc] at hx
    rcases eq_or_lt_of_le hx.1 with hxe | hxl
    · have hxx : x = mx S - stair S := by omega
      rw [hxx]; exact hmem
    · exact stair_block_sub_self h0 hne (by simp only [Finset.mem_Icc]; omega)

