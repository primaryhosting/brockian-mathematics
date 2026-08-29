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

private lemma decompB (ht : t.Nonempty) :
    t = (t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t + 1) (mx t) := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · intro hx
    by_cases hc : x ≤ mx t - run t
    · exact Or.inl ⟨hx, hc⟩
    · exact Or.inr ⟨by omega, le_mx hx⟩
  · rintro (⟨hx, -⟩ | ⟨h1, h2⟩)
    · exact hx
    · exact Icc_run_subset ht (Finset.mem_Icc.mpr ⟨h1, h2⟩)

