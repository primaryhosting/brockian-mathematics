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

theorem frankDown_nonempty (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : (frankDown s).Nonempty := by
  have hmn_pos : 1 ≤ mn s := by
    have hmem := mn_mem hne
    have hne0 : mn s ≠ 0 := fun h => h0 (h ▸ hmem)
    omega
  have himp : mx s + 2 - mn s ≤ mx s + 1 := by
    have : mx s + 2 ≤ mx s + 1 + mn s := by omega
    omega
  exact ⟨mx s + 1, by
    unfold frankDown
    simp [himp]⟩

