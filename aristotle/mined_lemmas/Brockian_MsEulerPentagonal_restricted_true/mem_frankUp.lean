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

theorem mem_frankUp {s : Finset ℕ} {x : ℕ} :
    x ∈ frankUp s ↔
      (x = run s ∨ (x ∈ s ∧ ¬ (mx s + 1 - run s ≤ x ∧ x ≤ mx s)) ∨
        (mx s - run s ≤ x ∧ x ≤ mx s - 1)) := by
  simp [frankUp, Finset.mem_insert, Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]

/-
In the "Down" case write `a := mx s`, `b := mn s`, `r := run s` and `I := Icc (a + 1 - b) a`.
The hypotheses give `1 ≤ b`, `b ≤ r ≤ a`, `2 * b ≤ a`, `I ⊆ s` (`Icc_mn_subset`), `b ∉ I`,
`#I = b`, `b ∈ s`, `a ∈ s` and `∀ x ∈ s, b ≤ x ∧ x ≤ a`.  By definition
`frankDown s = ((s.erase b) \ I) ∪ Icc (a + 2 - b) (a + 1)`, a union of two disjoint sets, and
`Icc (a + 2 - b) (a + 1) = Icc ((a + 1 - b) + 1) (a + 1)` has the same cardinality `b` as `I`
while `sum_Icc_shift` gives that its sum is `(∑ i ∈ I, i) + b`.  Combined with
`Finset.sum_sdiff`, `Finset.card_sdiff` and `Finset.add_sum_erase` this yields
`frankDown_sum` and `frankDown_card`.  Membership in `frankDown s` is `mem_frankDown`.
-/

section Down

variable {s : Finset ℕ}

