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

theorem frankUp_mx (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : mx (frankUp s) = mx s - 1 := by
  have h1 : 1 ≤ run s := one_le_run h0
  have hb : mn s ≤ mx s := mn_le (mx_mem hne)
  refine le_antisymm ?_ ?_
  · refine Finset.sup_le ?_
    intro x hx
    rw [mem_frankUp] at hx
    simp only [id_eq]
    rcases hx with rfl | ⟨hxs, hxn⟩ | ⟨hl, hr⟩
    · omega
    · have hle := le_mx hxs
      rcases not_and_or.mp hxn with h' | h' <;> omega
    · omega
  · refine le_mx ?_
    rw [mem_frankUp]
    exact Or.inr (Or.inr ⟨by omega, by omega⟩)

