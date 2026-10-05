import Mathlib

/-!
# Franklin's involution and the pentagonal number theorem (combinatorial core)

A partition of `n` into distinct positive parts is encoded as a `Finset ℕ` not containing `0`
whose sum is `n`.  The main result of this file, `Franklin.sum_sign_DP`, is Franklin's theorem:
the signed count `∑ (-1)^(number of parts)` over all partitions of `n` into distinct parts is
`(-1)^k` if `n` is a generalized pentagonal number `k(3k∓1)/2`, and `0` otherwise.
-/

namespace Franklin

open Finset

/-- Partitions of `n` into distinct positive parts, encoded as finsets of positive naturals. -/

lemma op1_op2 (h0 : 0 ∉ t) (hB : IsB t) : op1 (op2 t) = t := by
  have h2 := IsB.two_run_lt_mx h0 hB
  have h1 := run_pos h0
  have hmn := op2_mn h0 hB
  have hmx := op2_mx h0 hB
  have herase : (op2 t).erase (mn (op2 t))
      = (t.filter (fun x => x ≤ mx t - run t)) ∪ Finset.Icc (mx t - run t) (mx t - 1) := by
    rw [hmn, op2_eq, Finset.erase_insert (run_notMemB h0 hB)]
  have hfilter : ((op2 t).erase (mn (op2 t))).filter (fun x => x ≤ mx (op2 t) - mn (op2 t))
      = t.filter (fun x => x ≤ mx t - run t) := by
    rw [herase, hmn, hmx]
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨h3 | h3, h4⟩
      · exact h3
      · omega
    · intro h3
      have := memL'_lt h0 (Finset.mem_filter.mpr h3)
      exact ⟨Or.inl h3, by omega⟩
  have hIccEq : Finset.Icc (mx (op2 t) - mn (op2 t) + 2) (mx (op2 t) + 1)
      = Finset.Icc (mx t - run t + 1) (mx t) := by
    rw [hmn, hmx]
    congr 1
    · omega
    · omega
  conv_rhs => rw [decompB hB.1]
  rw [op1_eq, hfilter, hIccEq]

end BSide

section Cancellation

/-- Franklin's involution cancels the sets admitting the first move against those admitting
the second move. -/
