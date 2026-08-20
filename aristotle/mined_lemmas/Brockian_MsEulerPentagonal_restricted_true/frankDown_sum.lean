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

theorem frankDown_sum (h0 : 0 ∉ s) (hne : s.Nonempty) (hbr : mn s ≤ run s)
    (hab : 2 * mn s ≤ mx s) : ∑ i ∈ frankDown s, i = ∑ i ∈ s, i := by
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hbs : mn s ∈ s := mn_mem hne
  have hI := Icc_mn_subset hne hbr
  have hbI := mn_notMem_Icc h0 hne hab
  have hIe : Icc (mx s + 1 - mn s) (mx s) ⊆ s.erase (mn s) := fun x hx ↦
    Finset.mem_erase.mpr ⟨fun h ↦ hbI (h ▸ hx), hI hx⟩
  have hdisj : Disjoint (s.erase (mn s) \ Icc (mx s + 1 - mn s) (mx s))
      (Icc (mx s + 2 - mn s) (mx s + 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_Icc] at hx hx2
    exact hx.2 ⟨by omega, le_mx hx.1.2⟩
  rw [frankDown, Finset.sum_union hdisj]
  have hJ : Icc (mx s + 2 - mn s) (mx s + 1) = Icc ((mx s + 1 - mn s) + 1) (mx s + 1) := by
    congr 1
    omega
  rw [hJ, sum_Icc_shift (mx s + 1 - mn s) (mx s)]
  have h1 : ∑ i ∈ s.erase (mn s) \ Icc (mx s + 1 - mn s) (mx s), i
      + ∑ i ∈ Icc (mx s + 1 - mn s) (mx s), i = ∑ i ∈ s.erase (mn s), i :=
    Finset.sum_sdiff hIe
  have h2 : ∑ i ∈ s.erase (mn s), i + mn s = ∑ i ∈ s, i :=
    Finset.sum_erase_add s (fun i ↦ i) hbs
  omega

