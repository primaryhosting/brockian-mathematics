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

theorem Efin_of_pent {n : ℕ} {k : ℤ} (hk : 2 * (n : ℤ) = k * (3 * k - 1)) :
    Efin n = (-1 : ℤ) ^ k.natAbs := by
  rw [Efin_eq_sum_notGood]
  have h1 : (DP n).filter (fun s ↦ ¬ Good s) = {pentSet k} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨pentSet_mem_DP hk, pentSet_not_good k⟩
    · intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
      obtain ⟨l, hl, rfl⟩ := notGood_param ht1 ht2
      rw [pent_inj (by omega : l * (3 * l - 1) = k * (3 * k - 1))]
  rw [h1, Finset.sum_singleton, pentSet_card]

