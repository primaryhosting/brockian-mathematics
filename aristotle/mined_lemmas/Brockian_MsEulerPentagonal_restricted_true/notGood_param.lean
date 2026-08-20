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

theorem notGood_param {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : ¬ Good s) :
    ∃ k : ℤ, 2 * (n : ℤ) = k * (3 * k - 1) ∧ s = pentSet k := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  rcases notGood_classify' hs hg with rfl | ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · refine ⟨0, ?_, ?_⟩
    · simp at hsum
      simp [← hsum]
    · simp [pentSet]
  · refine ⟨(k : ℤ), ?_, ?_⟩
    · have h1 := sum_Icc_stair1 hk
      rw [hsum] at h1
      have : ((2 * n : ℕ) : ℤ) = ((k * (3 * k - 1) : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast [Nat.cast_sub (by omega : 1 ≤ 3 * k)] at this
      linarith
    · rw [pentSet, if_pos (by exact_mod_cast hk : (0 : ℤ) < (k : ℤ))]
      simp
  · refine ⟨-(k : ℤ), ?_, ?_⟩
    · have h1 := sum_Icc_stair2 k
      rw [hsum] at h1
      have : ((2 * n : ℕ) : ℤ) = ((k * (3 * k + 1) : ℕ) : ℤ) := by exact_mod_cast h1
      push_cast at this
      linarith
    · have h0' : ¬ (0 < -(k : ℤ)) := by omega
      rw [pentSet, if_neg h0']
      have : (-(k : ℤ)).natAbs = k := by omega
      rw [this]

/-- Any exceptional partition of `n` witnesses that `n` is a generalized pentagonal number. -/
