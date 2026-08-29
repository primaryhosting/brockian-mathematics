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

private lemma run_notMemB (h0 : 0 ∉ t) (hB : IsB t) :
    run t ∉ (t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t) (mx t - 1) := by
  have h2 := IsB.two_run_lt_mx h0 hB
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, not_or]
  refine ⟨?_, ?_⟩
  · rintro ⟨hmem, -⟩
    exact absurd (mn_le hB.1 hmem) (by have := hB.2.1; omega)
  · rintro ⟨h, -⟩; omega

