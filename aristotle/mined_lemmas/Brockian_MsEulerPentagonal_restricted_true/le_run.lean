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

theorem le_run {s : Finset ℕ} {r : ℕ} (h0 : 0 ∉ s)
    (h : Icc (mx s + 1 - r) (mx s) ⊆ s) : r ≤ run s := by
  unfold run
  by_contra hc
  push_neg at hc
  -- The set is nonempty (mx s is in it, since mx s >= 1 when 0 ∉ s and s nonempty, and mx s - mx s = 0 ∉ s)
  have hne : {r | 1 ≤ r ∧ mx s - r ∉ s}.Nonempty := by
    use mx s + 1
    simp
    exact h0
  -- sInf is in the set
  have hsmem := Nat.sInf_mem hne
  -- Let k = sInf {...}
  set k := sInf {r | 1 ≤ r ∧ mx s - r ∉ s} with hk_def
  -- From hsmem, k satisfies the predicate
  rw [hk_def] at hsmem
  obtain ⟨hk1, hkn⟩ := hsmem
  -- k < r from hc
  -- So mx s - k ≥ mx s + 1 - r (since k ≤ r - 1)
  -- And mx s - k ≤ mx s (since k ≥ 1)
  -- Therefore mx s - k ∈ Icc (mx s + 1 - r) (mx s), so by h, mx s - k ∈ s
  -- But hkn says mx s - k ∉ s - contradiction!
  have hklt : k < r := hc
  have hIcc : mx s - k ∈ Icc (mx s + 1 - r) (mx s) := by
    simp [Finset.mem_Icc]
    omega
  exact hkn (h hIcc)

