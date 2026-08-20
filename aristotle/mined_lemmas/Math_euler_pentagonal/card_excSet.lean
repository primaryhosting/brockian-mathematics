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

lemma card_excSet (k : ℤ) : (excSet k).card = k.natAbs := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · rw [excSet, if_neg (by omega), if_pos hk, Nat.card_Icc]
    omega
  · subst hk; simp [excSet]
  · rw [excSet, if_pos hk, Nat.card_Icc]
    have : 1 ≤ k.natAbs := by omega
    omega

