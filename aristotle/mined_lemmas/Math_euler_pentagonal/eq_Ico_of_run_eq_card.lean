import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/

lemma eq_Ico_of_run_eq_card {s : Finset ℕ} (hs : s.Nonempty) (h0 : 0 ∉ s)
    (h : run s = s.card) : s = Finset.Ico (mx s - s.card + 1) (mx s + 1) := by
  have hsub : Finset.Icc (mx s - run s + 1) (mx s) ⊆ s := Icc_run_subset hs
  have hcard : (Finset.Icc (mx s - run s + 1) (mx s)).card = run s := card_Icc_run hs h0
  have heq : Finset.Icc (mx s - run s + 1) (mx s) = s :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [h] at heq
  exact heq.symm.trans (Finset.Ico_add_one_right_eq_Icc _ _).symm

/-- The staircases `{k, …, 2k-1}`. -/
