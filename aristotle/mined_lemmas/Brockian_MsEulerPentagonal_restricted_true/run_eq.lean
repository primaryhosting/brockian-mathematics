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

theorem run_eq {s : Finset ℕ} {r : ℕ} (h1 : 1 ≤ r) (h2 : Icc (mx s + 1 - r) (mx s) ⊆ s)
    (h3 : (mx s - r) ∉ s) : run s = r := by
  have hne : {q : ℕ | 1 ≤ q ∧ (mx s - q) ∉ s}.Nonempty := ⟨r, h1, h3⟩
  have hmem : 1 ≤ run s ∧ (mx s - run s) ∉ s := Nat.sInf_mem hne
  refine le_antisymm (Nat.sInf_le ⟨h1, h3⟩) ?_
  by_contra hc
  push_neg at hc
  exact hmem.2 (h2 (Finset.mem_Icc.mpr ⟨by omega, by omega⟩))

/-- Shifting an interval by one. -/
