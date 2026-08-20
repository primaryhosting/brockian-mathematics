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

theorem frankDown_frankUp (h0 : 0 ∉ s) (hne : s.Nonempty) (hrb : run s < mn s)
    (hab : 2 * run s < mx s) : frankDown (frankUp s) = s := by
  have h1r : 1 ≤ run s := one_le_run h0
  have hb1 : 1 ≤ mn s := Nat.pos_of_ne_zero (fun h ↦ h0 (h ▸ mn_mem hne))
  have hba : mn s ≤ mx s := mn_le (mx_mem hne)
  have hrmx : run s ≤ mx s := run_le h0 hne
  have hI := Icc_run_subset hne
  have hnot := run_notMem h0
  have hmx := frankUp_mx h0 hne hrb hab
  have hmn := frankUp_mn h0 hrb hab
  ext x
  rw [mem_frankDown, hmx, hmn, mem_frankUp]
  constructor
  · rintro (⟨hxt, hxne, hxn⟩ | ⟨hl, hr⟩)
    · rcases hxt with rfl | ⟨hxs, -⟩ | ⟨hl, hr⟩
      · exact absurd rfl hxne
      · exact hxs
      · exact absurd ⟨by omega, by omega⟩ hxn
    · exact hI (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · intro hx
    have hxb := mn_le hx
    have hxa := le_mx hx
    by_cases hcase : mx s + 1 - run s ≤ x
    · right
      exact ⟨by omega, by omega⟩
    · left
      have hxne : x ≠ mx s - run s := fun h ↦ hnot (h ▸ hx)
      refine ⟨Or.inr (Or.inl ⟨hx, ?_⟩), by omega, ?_⟩
      · rintro ⟨hl, -⟩
        omega
      · rintro ⟨hl, -⟩
        omega

end Up

