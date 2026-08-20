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

lemma sl_nonempty (s : Finset ℕ) (h0 : 0 ∉ s) : {j | mx s - j ∉ s}.Nonempty :=
  ⟨mx s + 1, by simpa using h0⟩

