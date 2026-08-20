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

theorem Efin_eq_sum_notGood (n : ℕ) :
    Efin n = ∑ s ∈ (DP n).filter (fun s ↦ ¬ Good s), (-1 : ℤ) ^ s.card := by
  have hzero : ∑ s ∈ (DP n).filter (fun s ↦ Good s), (-1 : ℤ) ^ s.card = 0 := by
    refine Finset.sum_involution (fun s _ ↦ frank s) ?_ ?_ ?_ ?_
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      rw [frank_sign ha1 ha2]
      ring
    · intro a ha _ heq
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      have heq' : frank a = a := heq
      have hsg := frank_sign ha1 ha2
      rw [heq'] at hsg
      have hne0 : ((-1 : ℤ)) ^ a.card ≠ 0 := pow_ne_zero _ (by norm_num)
      exact hne0 (by linarith)
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact Finset.mem_filter.mpr ⟨frank_mem ha1 ha2, frank_good ha1 ha2⟩
    · intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_filter.mp ha
      exact frank_frank ha1 ha2
  have hsplit := Finset.sum_filter_add_sum_filter_not (DP n) (fun s ↦ Good s)
    (fun s ↦ (-1 : ℤ) ^ s.card)
  rw [hzero, zero_add] at hsplit
  rw [Efin, ← hsplit]

/-- Any exceptional partition is one of the two "pentagonal staircases". -/
