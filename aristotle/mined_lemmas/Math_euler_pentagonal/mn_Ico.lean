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

lemma mn_Ico {a b : ℕ} (h : a < b) : mn (Finset.Ico a b) = a := by
  have hne : (Finset.Ico a b).Nonempty := ⟨a, Finset.mem_Ico.mpr ⟨le_refl _, h⟩⟩
  simp only [mn, dif_pos hne]
  refine le_antisymm (Finset.min'_le _ _ (Finset.mem_Ico.mpr ⟨le_refl _, h⟩)) ?_
  exact Finset.le_min' _ _ _ (fun y hy => (Finset.mem_Ico.mp hy).1)

