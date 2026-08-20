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

theorem hasProd_pf :
    HasProd (fun i ↦ ∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j))
      (PowerSeries.mk fun n ↦ (pf n : ℤ)) := by
  have := Nat.Partition.hasProd_powerSeriesMk_card_restricted ℤ (fun _ ↦ True)
  simp [pf, restricted_true] at this ⊢
  convert this using 2

-- Specialize `Nat.Partition.hasProd_genFun (fun _ c ↦ if c = 1 then (-1 : ℤ) else 0)`:
-- the `i`-th factor is `1 + ∑' j, (if j + 1 = 1 then -1 else 0) • X ^ ((i+1)*(j+1)) = 1 - X^(i+1)`
-- (use `tsum_eq_single 0`), and `Nat.Partition.genFun f = PowerSeries.mk Edist` because
-- `p.parts.toFinsupp.prod f` is `(-1) ^ (Multiset.card p.parts)` when `p.parts.Nodup` and `0`
-- otherwise.
