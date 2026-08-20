import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/

lemma isExc_empty : IsExc (∅ : Finset ℕ) := by
  rw [IsExc, if_pos (by rw [mn_empty, sl_empty]), mx_empty, mn_empty]

/-- The exceptional configurations of Franklin's involution, indexed by `k : ℤ`. -/
