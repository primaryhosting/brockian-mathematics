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

theorem frankDown_mx (h0 : 0 ∉ s) (hne : s.Nonempty)
    (hab : 2 * mn s ≤ mx s) : mx (frankDown s) = mx s + 1 := by
  apply le_antisymm
  · -- All elements of frankDown s are ≤ mx s + 1
    apply Finset.sup_le
    intro x hx
    rw [mem_frankDown] at hx
    rcases hx with ⟨hx_s, _, _⟩ | ⟨hx_lb, hx_ub⟩
    · exact le_trans (le_mx hx_s) (Nat.le_succ _)
    · exact hx_ub
  · -- mx s + 1 ∈ frankDown s
    have hmn : 1 ≤ mn s := Nat.one_le_iff_ne_zero.mpr (fun h => h0 (by simpa [h] using mn_mem hne))
    have hmem : mx s + 1 ∈ frankDown s := by
      rw [mem_frankDown]
      right
      constructor
      · omega
      · rfl
    unfold mx
    exact Finset.le_sup hmem (f := id)

