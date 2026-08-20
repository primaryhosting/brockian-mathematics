/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma stair_le_card (h0 : 0 ∉ S) (hne : S.Nonempty) : stair S ≤ S.card := by
  have := Finset.card_le_card (stair_block_sub_self h0 hne)
  rwa [card_stair_block] at this

