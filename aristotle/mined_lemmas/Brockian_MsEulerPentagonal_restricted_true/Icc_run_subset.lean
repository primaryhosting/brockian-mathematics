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

theorem Icc_run_subset {s : Finset ℕ} (hs : s.Nonempty) :
    Icc (mx s + 1 - run s) (mx s) ⊆ s := by
  intro k hk
  by_cases hkmx : k = mx s
  · rw [hkmx]
    exact mx_mem hs
  · simp only [Finset.mem_Icc] at hk
    have hklt : k < mx s := lt_of_le_of_ne hk.2 hkmx
    have hr' : mx s - k < run s := by omega
    have hr'_ge : 1 ≤ mx s - k := by omega
    have hnotin : mx s - (mx s - k) ∈ s := by
      by_contra hc
      have hle : run s ≤ mx s - k := Nat.sInf_le ⟨hr'_ge, hc⟩
      omega
    rwa [Nat.sub_sub_self (le_of_lt hklt)] at hnotin

/-- Characterisation of `run`. -/
