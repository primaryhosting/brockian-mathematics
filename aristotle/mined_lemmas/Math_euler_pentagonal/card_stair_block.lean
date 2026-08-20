/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma card_stair_block : (Finset.Icc (mx S + 1 - stair S) (mx S)).card = stair S := by
  have := stair_le_mx (S := S)
  rw [Nat.card_Icc]
  omega

