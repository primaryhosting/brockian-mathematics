/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma two_mn_le_mx (h0 : 0 ∉ S) (hne : S.Nonempty) (hA : mn S ≤ stair S) (hnex : ¬ IsExc S) :
    2 * mn S ≤ mx S := by
  by_contra hcon
  push_neg at hcon
  have hs1 : 1 ≤ mn S := one_le_mn h0 hne
  have hsM : mn S ≤ mx S := mn_le_mx hne
  have hblock : Finset.Icc (mx S + 1 - stair S) (mx S) ⊆ S := stair_block_sub_self h0 hne
  have hsub : Finset.Icc (mn S) (mx S) ⊆ S := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    exact hblock (by simp only [Finset.mem_Icc]; omega)
  have hSeq : S = Finset.Icc (mn S) (mx S) := Finset.Subset.antisymm subset_Icc_mn_mx hsub
  have hstle : stair S ≤ mx S + 1 - mn S := by
    have := hblock (show mx S + 1 - stair S ∈ Finset.Icc (mx S + 1 - stair S) (mx S) by
      simp only [Finset.mem_Icc]; have := stair_le_mx (S := S); omega)
    have hmm := mn_le S this
    have := stair_le_mx (S := S)
    omega
  have hstge : mx S + 1 - mn S ≤ stair S := by
    have hsub2 : Finset.Icc (mx S + 1 - (mx S + 1 - mn S)) (mx S) ⊆ S := by
      intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hsub (by simp only [Finset.mem_Icc]; omega)
    unfold stair
    exact Nat.le_findGreatest (by omega) hsub2
  have hMeq : mx S = 2 * mn S - 1 := by omega
  refine hnex ⟨mn S, hs1, Or.inl ?_⟩
  rw [← hMeq]
  exact hSeq

/-- The properties of Franklin's move in case A. -/
