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

lemma sl_eq {s : Finset ℕ} {j : ℕ} (h1 : mx s - j ∉ s) (h2 : ∀ i < j, mx s - i ∈ s) :
    sl s = j := by
  have hle : sl s ≤ j := Nat.sInf_le h1
  refine le_antisymm hle ?_
  by_contra h
  push_neg at h
  have hmem : sInf {j | mx s - j ∉ s} ∈ {j | mx s - j ∉ s} := Nat.sInf_mem ⟨j, h1⟩
  exact hmem (h2 _ h)

