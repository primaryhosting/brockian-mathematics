import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/

theorem genFun_fsgn_eq : Nat.Partition.genFun fsgn = PowerSeries.mk pentagonalCoeff := by
  ext n
  rw [Nat.Partition.coeff_genFun, PowerSeries.coeff_mk, pentagonalCoeff,
    ← Franklin.sum_sign_DP n, ← sum_distinct_eq_sum_DP n, Finset.sum_filter]
  exact Finset.sum_congr rfl (fun p _ => prod_fsgn n p)

/-- The product `∏ (1 - X^(i+1))` is the generating function attached to `fsgn`. -/
