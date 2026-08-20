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

theorem frankUp_mn (h0 : 0 ∉ s) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : mn (frankUp s) = run s := by
  have h1 : 1 ≤ run s := one_le_run h0
  refine le_antisymm ?_ ?_
  · refine mn_le ?_
    rw [mem_frankUp]
    exact Or.inl rfl
  · have hmem := mn_mem (frankUp_nonempty (s := s))
    rw [mem_frankUp] at hmem
    rcases hmem with h | ⟨hxs, -⟩ | ⟨hl, hr⟩
    · omega
    · have := mn_le hxs
      omega
    · omega

