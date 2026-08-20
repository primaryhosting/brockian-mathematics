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

theorem hasProd_Edist :
    HasProd (fun i ↦ (1 : ℤ⟦X⟧) - X ^ (i + 1)) (PowerSeries.mk fun n ↦ Edist n) := by
  have h := Nat.Partition.hasProd_genFun (fun _ c ↦ if c = 1 then (-1 : ℤ) else 0)
  have factor_eq : (fun i ↦ (1 : ℤ⟦X⟧) - X ^ (i + 1)) = (fun i ↦ 1 + ∑' (j : ℕ), (if j + 1 = 1 then (-1 : ℤ) else 0) • X ^ ((i + 1) * (j + 1))) := by
    ext i
    rw [tsum_eq_single 0]
    · simp [sub_eq_add_neg]
    · simp
  rw [factor_eq]
  have serie_eq : PowerSeries.mk (fun n ↦ Edist n) = Nat.Partition.genFun (fun x c => if c = 1 then (-1 : ℤ) else 0) := by
    ext n
    simp [Edist]
    have key : ∀ p : Nat.Partition n,
      (Multiset.toFinsupp p.parts).prod (fun x c => if c = 1 then (-1 : ℤ) else 0) =
      if p.parts.Nodup then (-1 : ℤ) ^ p.parts.card else 0 := by
      intro p
      by_cases h : p.parts.Nodup
      · simp [h]
        have support_eq : (Multiset.toFinsupp p.parts).support = p.parts.toFinset := by
          ext x
          simp [Multiset.mem_toFinset]
        have card_eq : (Multiset.toFinsupp p.parts).support.card = p.parts.card := by
          rw [support_eq]
          exact Multiset.toFinset_card_of_nodup h
        have prod_eq : ((Multiset.toFinsupp p.parts).prod fun x c => if c = 1 then (-1 : ℤ) else 0) =
                       ∏ x ∈ p.parts.toFinset, (-1 : ℤ) := by
          rw [← support_eq]
          apply Finset.prod_congr rfl
          intro x hx
          simp [Multiset.count_eq_one_of_mem h (Multiset.mem_toFinset.mp hx)]
        rw [prod_eq, Finset.prod_const, Multiset.toFinset_card_of_nodup h]
      · simp [h]
        rw [Multiset.nodup_iff_count_le_one] at h
        push_neg at h
        obtain ⟨a, ha⟩ := h
        exact ⟨a, Multiset.count_pos.mp (by linarith), ne_of_gt ha⟩
    simp_rw [key]
    rw [← Finset.sum_filter]
    congr
  rw [serie_eq]
  exact h

-- `hasProd_pf.mul hasProd_Edist` has all factors equal to `1`, by
-- `PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero` applied to
-- `f = X ^ (i + 1)` (after `pow_mul`); conclude with `HasProd.unique` against `hasProd_one`.
