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

theorem mem_DP {n : ℕ} {s : Finset ℕ} : s ∈ DP n ↔ 0 ∉ s ∧ ∑ i ∈ s, i = n := by
  simp only [DP]
  constructor
  · intro h
    exact Finset.mem_filter.mp h |>.2
  · intro ⟨h0, hsum⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, h0, hsum⟩
    rw [Finset.mem_powerset]
    intro x hx
    apply Finset.mem_range.mpr
    have hx_pos : 1 ≤ x := Nat.pos_of_ne_zero (fun h => h0 (h ▸ hx))
    have hx_le : x ≤ n := hsum ▸ Finset.single_le_sum (fun i _ => Nat.zero_le i) hx
    omega

/-- The signed count of partitions of `n` into distinct parts, in the finset encoding. -/
