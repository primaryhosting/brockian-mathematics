/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma card_pent2 {c : ℕ} (hc : 1 ≤ c) : (Finset.Icc (c + 1) (2 * c)).card = c := by
  rw [Nat.card_Icc]; omega

open scoped Classical in
