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

theorem hasProd_one_sub_X_pow :
    HasProd (fun i : ℕ => (1 : ℤ⟦X⟧) - X ^ (i + 1)) (Nat.Partition.genFun fsgn) := by
  have h := Nat.Partition.hasProd_genFun fsgn
  convert h using 2 with i
  rw [tsum_eq_single 0]
  · simp [fsgn]
    ring
  · intro b hb
    simp [fsgn, hb]

/-- **Euler's pentagonal number theorem.**  The infinite product `∏_{i ≥ 1} (1 - X^i)`, which is
the reciprocal of the generating function of the partition function, equals the pentagonal
number series `∑_{k} (-1)^k (X^(k(3k-1)/2) + X^(k(3k+1)/2))`. -/
