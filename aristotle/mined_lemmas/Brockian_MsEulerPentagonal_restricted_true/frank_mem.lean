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

theorem frank_mem {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : Good s) : frank s ∈ DP n := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  obtain ⟨hne, hd, hu⟩ := hg
  rw [mem_DP]
  by_cases h : mn s ≤ run s
  · simp only [frank, if_pos h]
    exact ⟨frankDown_zero h0 hne, by rw [frankDown_sum h0 hne h (hd h), hsum]⟩
  · simp only [frank, if_neg h]
    rw [not_le] at h
    exact ⟨frankUp_zero h0 (hu h), by rw [frankUp_sum h0 hne h (hu h), hsum]⟩

