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

theorem conv_zero (n : ℕ) (hn : 0 < n) :
    ∑ j ∈ range (n + 1), Edist j * (pf (n - j) : ℤ) = 0 := by
  have h := congrArg (PowerSeries.coeff n) pf_mul_Edist
  rw [PowerSeries.coeff_mul] at h
  simp only [PowerSeries.coeff_mk] at h
  rw [PowerSeries.coeff_one, if_neg (by omega : ¬ n = 0)] at h
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j ↦ (pf i : ℤ) * Edist j)] at h
  have hr := Finset.sum_range_reflect (fun i ↦ (pf i : ℤ) * Edist (n - i)) (n + 1)
  rw [← hr] at h
  rw [← h]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  have hnj : n + 1 - 1 - j = n - j := by omega
  have h2 : n - (n - j) = j := by omega
  rw [hnj, h2]
  ring

end PartA

section PartB

/-- Partitions of `n` into distinct parts, encoded as finsets of positive naturals. -/
