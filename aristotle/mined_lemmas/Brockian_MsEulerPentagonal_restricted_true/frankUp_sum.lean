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

theorem frankUp_sum (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : ∑ i ∈ frankUp s, i = ∑ i ∈ s, i := by
  have h1r : 1 ≤ run s := one_le_run h0
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hrmx : run s ≤ mx s := run_le h0 hne
  have hI := Icc_run_subset hne
  have hnot := run_notMem h0
  have hrs : run s ∉ s := fun h ↦ absurd (mn_le h) (by omega)
  have hdisj : Disjoint (s \ Icc (mx s + 1 - run s) (mx s)) (Icc (mx s - run s) (mx s - 1)) := by
    rw [Finset.disjoint_left]
    intro x hx hx2
    simp only [Finset.mem_sdiff, Finset.mem_Icc] at hx hx2
    have hxne : x ≠ mx s - run s := fun h ↦ hnot (h ▸ hx.1)
    exact hx.2 ⟨by omega, by omega⟩
  have hrnot : run s ∉ (s \ Icc (mx s + 1 - run s) (mx s)) ∪ Icc (mx s - run s) (mx s - 1) := by
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_Icc]
    rintro (⟨hx, -⟩ | ⟨hl, hr⟩)
    · exact hrs hx
    · omega
  rw [frankUp, Finset.sum_insert hrnot, Finset.sum_union hdisj]
  have hIeq : Icc (mx s + 1 - run s) (mx s) = Icc ((mx s - run s) + 1) ((mx s - 1) + 1) := by
    congr 1 <;> omega
  have hsh := sum_Icc_shift (mx s - run s) (mx s - 1)
  rw [← hIeq] at hsh
  have h1 : ∑ i ∈ s \ Icc (mx s + 1 - run s) (mx s), i
      + ∑ i ∈ Icc (mx s + 1 - run s) (mx s), i = ∑ i ∈ s, i :=
    Finset.sum_sdiff hI
  omega

