import Mathlib

/-!
# Franklin's involution

Combinatorial core of Euler's pentagonal number theorem: the signed count of partitions of
`n` into distinct parts (sign `(-1)^(number of parts)`) is `0` unless `n` is a generalized
pentagonal number.

Partitions into distinct parts are encoded as finite sets of positive naturals.
-/

namespace EulerPentagonal

open Finset

/-- The largest element of `s` (junk value `0` for `s = ∅`). -/

lemma genFun_one_eq :
    Nat.Partition.genFun (fun _ _ => (1 : ℤ))
      = PowerSeries.mk (fun n => (Fintype.card (Nat.Partition n) : ℤ)) := by
  ext n
  rw [Nat.Partition.coeff_genFun, coeff_mk]
  simp [Finsupp.prod]

/-- **Euler's pentagonal number theorem for the partition generating function**: the pentagonal
series `∑_{k ∈ ℤ} (-1)^k X^(k(3k-1)/2)` is the multiplicative inverse of the generating function
`∑_n p(n) X^n` of the partition function. -/
