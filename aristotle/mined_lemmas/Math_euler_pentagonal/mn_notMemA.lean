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

private lemma mn_notMemA (h0 : 0 ∉ s) (hA : IsA s) :
    mn s ∉ ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)
      ∪ Finset.Icc (mx s - mn s + 1) (mx s)) := by
  have hM := IsA.two_mn_le_mx h0 hA
  have h1 := mn_pos hA.1 h0
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_Icc, not_or]
  constructor
  · rintro ⟨⟨h, -⟩, -⟩; exact h rfl
  · rintro ⟨h, -⟩; omega

