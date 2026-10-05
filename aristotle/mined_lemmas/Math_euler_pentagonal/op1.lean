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

noncomputable def op1 (s : Finset ℕ) : Finset ℕ :=
  ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)) ∪ Finset.Icc (mx s - mn s + 2) (mx s + 1)

/-- Franklin's second move: subtract `1` from each of the `σ` largest parts (where `σ` is the
run length) and adjoin a new part equal to `σ`. -/
