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

theorem two_mul_pent (k : ℤ) : 2 * pent k = k * (3 * k - 1) := by
  have h : (2 : ℤ) ∣ k * (3 * k - 1) := by
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩ <;> subst hm
    · exact ⟨m * (3 * (m + m) - 1), by ring⟩
    · exact ⟨(2 * m + 1) * (3 * m + 1), by ring⟩
  rw [pent, Int.mul_ediv_cancel' h]

