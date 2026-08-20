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

lemma sum_excSet (k : ℤ) : (∑ x ∈ excSet k, x) = pentN k := by
  rcases lt_trichotomy k 0 with hk | hk | hk
  · have hj : 1 ≤ k.natAbs := by omega
    have hk' : (k.natAbs : ℤ) = -k := by omega
    rw [excSet, if_neg (by omega), if_pos hk]
    set j := k.natAbs with hjdef
    have hsum := two_sum_Icc (j + 1) (2 * j) (by omega)
    refine (pentN_of k _ ?_).symm
    have hc := congrArg (fun t : ℕ => (t : ℤ)) hsum
    push_cast at hc
    push_cast
    rw [show k = -(j : ℤ) by omega]
    linarith [hc]
  · subst hk
    simp [excSet, pentN]
  · have hj : 1 ≤ k.natAbs := by omega
    have hk' : (k.natAbs : ℤ) = k := by omega
    rw [excSet, if_pos hk]
    set j := k.natAbs with hjdef
    have hsum := two_sum_Icc j (2 * j - 1) (by omega)
    refine (pentN_of k _ ?_).symm
    have h2j : (2 * j - 1 : ℕ) + 1 = 2 * j := by omega
    rw [h2j] at hsum
    have hc := congrArg (fun t : ℕ => (t : ℤ)) hsum
    push_cast [Nat.cast_sub (show 1 ≤ 2 * j by omega), Nat.cast_sub (show 1 ≤ j by omega)] at hc
    push_cast
    rw [show k = (j : ℤ) by omega]
    linarith [hc]

