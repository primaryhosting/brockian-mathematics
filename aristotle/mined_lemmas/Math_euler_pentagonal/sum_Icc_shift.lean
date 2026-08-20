/-
Franklin's involution and the combinatorial core of Euler's pentagonal number theorem.
-/
import Mathlib

namespace EulerPentagonal

open Finset

/-- The minimum of a finset of naturals (`0` for the empty set). -/

lemma sum_Icc_shift (a b : ℕ) :
    ∑ i ∈ Finset.Icc (a + 1) (b + 1), i = (∑ i ∈ Finset.Icc a b, i) + (b + 1 - a) := by
  rw [← Finset.map_add_right_Icc a b 1, Finset.sum_map]
  simp [Finset.sum_add_distrib, Nat.card_Icc]

