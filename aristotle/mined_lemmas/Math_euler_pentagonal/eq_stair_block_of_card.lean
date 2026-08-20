/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma eq_stair_block_of_card (h0 : 0 ∉ S) (hne : S.Nonempty) (h : S.card = stair S) :
    S = Finset.Icc (mx S + 1 - stair S) (mx S) :=
  (Finset.eq_of_subset_of_card_le (stair_block_sub_self h0 hne)
    (by rw [card_stair_block, h])).symm

