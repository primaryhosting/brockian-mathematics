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

lemma pentN_le (k : ℤ) : k.natAbs ≤ pentN k := by
  have h := pentN_spec k
  have hj0 : (0 : ℤ) ≤ (k.natAbs : ℤ) := Int.natCast_nonneg _
  zify
  rw [Int.abs_eq_natAbs]
  rcases le_or_gt 0 k with hk | hk
  · have hk' : (k.natAbs : ℤ) = k := by omega
    nlinarith
  · have hk' : (k.natAbs : ℤ) = -k := by omega
    nlinarith

