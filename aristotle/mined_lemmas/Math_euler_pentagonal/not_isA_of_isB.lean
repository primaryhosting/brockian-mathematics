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

lemma not_isA_of_isB {s : Finset ℕ} (hB : IsB s) : ¬IsA s := by
  rintro ⟨-, hle, -⟩
  have := hB.2.1
  omega

/-- **Franklin's theorem** (the combinatorial form of Euler's pentagonal number theorem):
the number of partitions of `n` into an even number of distinct parts minus the number with an
odd number of distinct parts is `(-1)^k` when `n = k(3k±1)/2`, and `0` otherwise. -/
