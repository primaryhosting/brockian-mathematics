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

theorem coeff_tprod_one_sub (n : ℕ) :
    (coeff n) (∏' i : ℕ, (1 - (X : ℤ⟦X⟧) ^ (i + 1)))
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) (n : ℤ), if pentN k = n then (-1 : ℤ) ^ k.natAbs else 0 := by
  rw [hasProd_one_sub.tprod_eq, coeff_mk, W_eq]

/-! ### Relation with the generating function of the partition function -/

/-- Coefficients of the geometric series `∑_{j ≥ 1} X^(m j)`. -/
