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

theorem euler_pentagonal (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc (-(n:ℤ)) n,
      (if (k * (3 * k - 1) / 2) ≤ (n:ℤ) then
        (-1 : ℤ) ^ (k.natAbs) *
          (Fintype.card (Nat.Partition (n - (k * (3 * k - 1) / 2).toNat)) : ℤ)
       else 0) = 0 := by
  have hpent : ∀ k : ℤ, k * (3 * k - 1) / 2 = pent k := fun _ ↦ rfl
  have hpf : ∀ m : ℕ, (Fintype.card (Nat.Partition m) : ℤ) = (pf m : ℤ) := fun _ ↦ rfl
  simp only [hpent, hpf]
  rw [← Finset.sum_filter]
  have main : ∑ k ∈ (Finset.Icc (-(n:ℤ)) n).filter (fun k ↦ pent k ≤ (n:ℤ)),
      ((-1 : ℤ) ^ k.natAbs * (pf (n - (pent k).toNat) : ℤ))
      = ∑ j ∈ Finset.range (n + 1), Efin j * (pf (n - j) : ℤ) := by
    refine Finset.sum_of_injOn (fun k ↦ (pent k).toNat) ?_ ?_ ?_ ?_
    · intro a _ b _ hab
      have hab' : (pent a).toNat = (pent b).toNat := hab
      have ha := pent_nonneg a
      have hb := pent_nonneg b
      exact pent_injective (by omega)
    · intro k hk
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hk
      have h1 := pent_nonneg k
      show (pent k).toNat ∈ (↑(Finset.range (n + 1)) : Set ℕ)
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro j hj hnot
      have hjn : j ≤ n := by
        simp only [Finset.mem_range] at hj
        omega
      refine mul_eq_zero_of_left (Efin_of_not_pent ?_) _
      intro k hk
      apply hnot
      have h1 := two_mul_pent k
      have hpk : pent k = (j : ℤ) := by omega
      have habs := abs_le_of_pent_le (k := k) (n := n) (by omega)
      have habs' := abs_le.mp habs
      refine ⟨k, ?_, ?_⟩
      · simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc]
        exact ⟨⟨habs'.1, habs'.2⟩, by omega⟩
      · show (pent k).toNat = j
        omega
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_Icc] at hk
      have h1 := pent_nonneg k
      have h2 : 2 * (((pent k).toNat : ℕ) : ℤ) = k * (3 * k - 1) := by
        have := two_mul_pent k
        omega
      rw [Efin_of_pent h2]
  rw [main]
  have hc := conv_zero n hn
  simp only [Edist_eq_Efin] at hc
  exact hc

end PartC

end Brockian.MsEulerPentagonal

