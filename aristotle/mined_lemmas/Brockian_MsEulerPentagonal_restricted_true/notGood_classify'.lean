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

theorem notGood_classify' {n : ℕ} {s : Finset ℕ} (hs : s ∈ DP n) (hg : ¬ Good s) :
    s = ∅ ∨ (∃ k : ℕ, 1 ≤ k ∧ s = Icc k (2 * k - 1)) ∨
      (∃ k : ℕ, 1 ≤ k ∧ s = Icc (k + 1) (2 * k)) := by
  obtain ⟨h0, hsum⟩ := mem_DP.mp hs
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · exact Or.inl rfl
  right
  have key : (mn s ≤ run s ∧ mx s < 2 * mn s) ∨ (run s < mn s ∧ mx s ≤ 2 * run s) := by
    by_contra hc
    push_neg at hc
    exact hg ⟨hne, fun h ↦ by have := hc.1 h; omega, fun h ↦ by have := hc.2 h; omega⟩
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  rcases key with ⟨hbr, hab⟩ | ⟨hrb, hab⟩
  · left
    have hI := Icc_mn_subset hne hbr
    have hmem : mx s + 1 - mn s ∈ s := hI (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have h2 := mn_le hmem
    refine ⟨mn s, hb1, Finset.Subset.antisymm ?_ ?_⟩
    · intro x hx
      have h3 := mn_le hx
      have h4 := le_mx hx
      simp only [Finset.mem_Icc]
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · right
    have hr1 : 1 ≤ run s := one_le_run h0
    have hI := Icc_run_subset hne
    have hmem : mx s + 1 - run s ∈ s := hI (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    have h2 := mn_le hmem
    refine ⟨run s, hr1, Finset.Subset.antisymm ?_ ?_⟩
    · intro x hx
      have h3 := mn_le hx
      have h4 := le_mx hx
      simp only [Finset.mem_Icc]
      omega
    · intro x hx
      simp only [Finset.mem_Icc] at hx
      exact hI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

