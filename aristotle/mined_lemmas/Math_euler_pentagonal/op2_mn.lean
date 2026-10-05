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

lemma op2_mn (h0 : 0 ∉ t) (hB : IsB t) : mn (op2 t) = run t :=
  le_antisymm (mn_le (op2_nonempty h0 hB) (op2_mem h0 hB))
    (op2_ge h0 hB (mn_mem (op2_nonempty h0 hB)))

