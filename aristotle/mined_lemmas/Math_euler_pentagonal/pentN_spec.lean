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

lemma pentN_spec (k : ℤ) : 2 * (pentN k : ℤ) = k * (3 * k - 1) := by
  have hnn : 0 ≤ k * (3 * k - 1) := by
    rcases le_or_gt k 0 with h | h
    · nlinarith
    · nlinarith
  obtain ⟨c, hc⟩ : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with ⟨t, ht⟩ | ⟨t, ht⟩
    · exact ⟨t * (3 * k - 1), by subst ht; ring⟩
    · exact ⟨k * (3 * t + 1), by subst ht; ring⟩
  have hc0 : 0 ≤ c := by omega
  unfold pentN
  rw [hc, Int.mul_ediv_cancel_left _ (by norm_num), Int.toNat_of_nonneg hc0]

