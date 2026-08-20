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

theorem euler_pentagonal :
    HasSum (fun k : ℤ ↦ ((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k)
      (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1))) := by
  rw [hasProd_one_sub.tprod_eq]
  exact hasSum_pentagonal

/-- Coefficient form of Euler's pentagonal number theorem: the coefficient of `X^n` in
`∏_{i ≥ 1} (1 - X^i)` is `(-1)^k` if `n = k(3k-1)/2` for some `k ∈ ℤ`, and `0` otherwise. -/
