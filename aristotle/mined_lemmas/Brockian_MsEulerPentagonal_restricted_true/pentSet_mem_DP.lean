import Mathlib

/-!
# Euler's pentagonal number theorem (recurrence form)

The main result `euler_pentagonal` states that for `n > 0`,
`∑ k (-1)^k p(n - g k) = 0` where `g k = k (3k-1)/2` runs over the generalized pentagonal
numbers and `p` is the partition function.

The proof has three parts.

* Part A (generating functions): using Mathlib's machinery for partition generating functions,
  `(∑ p(n) Xⁿ) * (∑ E(n) Xⁿ) = 1`, where `E(n)` is the signed count of partitions of `n` into
  distinct parts, the sign being the parity of the number of parts.
* Part B (Franklin's involution): `E(n) = (-1)^k` if `2n = k(3k-1)` for some integer `k`, and
  `E(n) = 0` otherwise.
* Part C: assembling the two.
-/

namespace Brockian.MsEulerPentagonal

open Finset

noncomputable section PartA

open PowerSeries
open scoped PowerSeries.WithPiTopology

/-- The partition function. -/

theorem pentSet_mem_DP {n : ℕ} {k : ℤ} (h : 2 * (n : ℤ) = k * (3 * k - 1)) :
    pentSet k ∈ DP n := by
  rcases lt_trichotomy k 0 with hk | rfl | hk
  · have h0 : ¬ (0 < k) := by omega
    rw [pentSet, if_neg h0]
    refine stair2_mem_DP (by omega) ?_
    have hk' : (k.natAbs : ℤ) = -k := by omega
    have : 2 * (n : ℤ) = (k.natAbs : ℤ) * (3 * (k.natAbs : ℤ) + 1) := by
      rw [hk']; linarith [h]
    exact_mod_cast this
  · have hn : n = 0 := by simpa using h
    have : pentSet 0 = (∅ : Finset ℕ) := by simp [pentSet]
    rw [this, hn, mem_DP]
    simp
  · rw [pentSet, if_pos hk]
    refine stair1_mem_DP (by omega) ?_
    have hk' : (k.toNat : ℤ) = k := by omega
    have h1 : 1 ≤ k.toNat := by omega
    have : 2 * (n : ℤ) = (k.toNat : ℤ) * (3 * (k.toNat : ℤ) - 1) := by rw [hk']; exact h
    have hcast : ((3 * k.toNat - 1 : ℕ) : ℤ) = 3 * (k.toNat : ℤ) - 1 := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * k.toNat)]
      ring
    have := this
    zify [Nat.cast_sub (by omega : 1 ≤ 3 * k.toNat)]
    linarith

/-- Every exceptional partition of `n` is `pentSet k` for a generalized pentagonal index `k`. -/
