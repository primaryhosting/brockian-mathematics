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

theorem frankUp_frankDown (h0 : 0 ∉ s) (hne : s.Nonempty) (hbr : mn s ≤ run s)
    (hab : 2 * mn s ≤ mx s) : frankUp (frankDown s) = s := by
  ext x
  rw [mem_frankUp, mem_frankDown]
  have hmx : mx (frankDown s) = mx s + 1 := frankDown_mx h0 hne hab
  have hrun : run (frankDown s) = mn s := frankDown_run h0 hne hab
  rw [hmx, hrun]
  ring_nf
  have h1 : 1 + mx s - 1 = mx s := by omega
  simp only [h1]
  have hmn_mem : mn s ∈ s := mn_mem hne
  have Himn : Icc (mx s + 1 - mn s) (mx s) ⊆ s := Icc_mn_subset hne hbr
  -- Key facts about elements of s
  have hle_mx : ∀ x ∈ s, x ≤ mx s := fun x hx => le_mx hx
  -- Simplify: mx s + 1 - mn s = 1 + mx s - mn s
  have heq1 : mx s + 1 - mn s = 1 + mx s - mn s := by omega
  constructor
  · intro hx
    rcases hx with rfl | ⟨hmid, hnotB⟩ | ⟨hx_lb, hx_ub⟩
    · exact hmn_mem
    · rcases hmid with hA | ⟨hB_lb, hB_ub⟩
      · exact hA.1
      · exact absurd ⟨hB_lb, hB_ub⟩ hnotB
    · exact Himn (Finset.mem_Icc.mpr ⟨by omega, hx_ub⟩)
  · intro hx
    by_cases hxeq : x = mn s
    · left; exact hxeq
    · by_cases hxIcc : 1 + mx s - mn s ≤ x ∧ x ≤ mx s
      · right; right; exact hxIcc
      · right; left
        have hlt : x < 1 + mx s - mn s := by
          by_contra hge
          push_neg at hge
          apply hxIcc
          exact ⟨hge, hle_mx x hx⟩
        constructor
        · left
          exact ⟨hx, hxeq, hxIcc⟩
        · simp only [not_and_or]
          left
          omega

end Down

/-
In the "Up" case write `a := mx s`, `b := mn s`, `r := run s`, `I := Icc (a + 1 - r) a` and
`J := Icc (a - r) (a - 1)`.  The hypotheses give `1 ≤ r < b ≤ a`, `2 * r < a`, `I ⊆ s`
(`Icc_run_subset`), `a - r ∉ s` (`run_notMem`), `#I = #J = r`, `r ∉ s`, `r < a - r`, and
`frankUp s = insert r ((s \ I) ∪ J)` where the three pieces are pairwise disjoint.
Since `I = Icc ((a - r) + 1) ((a - 1) + 1)`, `sum_Icc_shift` gives
`∑ i ∈ I, i = (∑ i ∈ J, i) + r`.  Membership in `frankUp s` is `mem_frankUp`.
-/

section Up

variable {s : Finset ℕ}

