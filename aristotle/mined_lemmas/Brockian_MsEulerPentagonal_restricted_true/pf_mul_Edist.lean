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

theorem pf_mul_Edist :
    (PowerSeries.mk fun n ↦ (pf n : ℤ)) * (PowerSeries.mk fun n ↦ Edist n) = 1 := by
  have h := hasProd_pf.mul hasProd_Edist
  have hone : ∀ i : ℕ, (∑' j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j)) * (1 - X ^ (i + 1)) = 1 := by
    intro i
    have hp : ∀ j : ℕ, (X : ℤ⟦X⟧) ^ ((i + 1) * j) = (X ^ (i + 1)) ^ j := fun j ↦ by
      rw [← pow_mul]
    simp only [hp]
    exact PowerSeries.WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)
  simp only [hone] at h
  exact (HasProd.unique h hasProd_one)

/-- Euler's recurrence: the convolution of the partition function with the signed count of
distinct partitions vanishes in positive degrees. -/
