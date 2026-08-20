/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma mn_lt_of_stair_lt_card (h0 : 0 ∉ S) (hne : S.Nonempty) (h : stair S < S.card) :
    mn S < mx S - stair S := by
  have hmem := mn_mem S hne
  have hblock := stair_block_sub_self h0 hne
  have hnot := stair_not_mem h0 hne
  have hst := stair_le_mx (S := S)
  -- the minimum is not in the top block
  have hnb : mn S ∉ Finset.Icc (mx S + 1 - stair S) (mx S) := by
    intro hin
    simp only [Finset.mem_Icc] at hin
    have : Finset.Icc (mn S) (mx S) ⊆ S := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hblock (by simp only [Finset.mem_Icc]; omega)
    have hSeq : S = Finset.Icc (mn S) (mx S) :=
      Finset.Subset.antisymm subset_Icc_mn_mx this
    have hcard : S.card = mx S + 1 - mn S := by
      rw [show S.card = (Finset.Icc (mn S) (mx S)).card from congrArg Finset.card hSeq,
        Nat.card_Icc]
    have hle : mx S + 1 - mn S ≤ stair S := by
      have hsub2 : Finset.Icc (mx S + 1 - (mx S + 1 - mn S)) (mx S) ⊆ S := by
        intro x hx
        simp only [Finset.mem_Icc] at hx
        exact this (by simp only [Finset.mem_Icc]; omega)
      unfold stair
      exact Nat.le_findGreatest (by omega) hsub2
    omega
  simp only [Finset.mem_Icc, not_and_or, not_le] at hnb
  have hle : mn S ≤ mx S := mn_le_mx hne
  have hne' : mn S ≠ mx S - stair S := by
    intro hcon; exact hnot (hcon ▸ hmem)
  omega

