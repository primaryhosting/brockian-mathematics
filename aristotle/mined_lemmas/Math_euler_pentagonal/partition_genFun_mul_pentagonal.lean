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

theorem partition_genFun_mul_pentagonal :
    (PowerSeries.mk (fun n => (Fintype.card (Nat.Partition n) : ℤ)))
        * (∑' k : ℤ, ((-1 : ℤ) ^ k.natAbs) • (X : ℤ⟦X⟧) ^ pentN k) = 1 := by
  have hG : HasProd (fun i : ℕ ↦ (1 : ℤ⟦X⟧) + ∑' j : ℕ, (1 : ℤ) • X ^ ((i + 1) * (j + 1)))
      (Nat.Partition.genFun (fun _ _ => (1 : ℤ))) := Nat.Partition.hasProd_genFun _
  have hmul := hG.mul hasProd_one_sub
  have hone : ∀ i : ℕ,
      ((1 : ℤ⟦X⟧) + ∑' j : ℕ, (1 : ℤ) • X ^ ((i + 1) * (j + 1))) * (1 - X ^ (i + 1)) = 1 :=
    fun i => geom_mul_one_sub (Nat.succ_ne_zero i)
  simp_rw [hone] at hmul
  have h1 : Nat.Partition.genFun (fun _ _ => (1 : ℤ)) * PowerSeries.mk W = 1 :=
    hmul.unique hasProd_one
  rw [hasSum_pentagonal.tsum_eq, ← genFun_one_eq]
  exact h1

end Math

