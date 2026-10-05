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

lemma op2_op1 (h0 : 0 ∉ s) (hA : IsA s) : op2 (op1 s) = s := by
  have hM := IsA.two_mn_le_mx h0 hA
  have hpos := mn_pos hA.1 h0
  have hmx := op1_mx h0 hA
  have hrun := op1_run h0 hA
  have hfilter : (op1 s).filter (fun x => x ≤ mx (op1 s) - run (op1 s))
      = (s.erase (mn s)).filter (fun x => x ≤ mx s - mn s) := by
    rw [hmx, hrun, op1_eq]
    ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_Icc, Finset.mem_erase]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact h1
      · omega
    · rintro ⟨h1, h2⟩
      exact ⟨Or.inl ⟨h1, h2⟩, by omega⟩
  have hIccEq : Finset.Icc (mx (op1 s) - run (op1 s)) (mx (op1 s) - 1)
      = Finset.Icc (mx s - mn s + 1) (mx s) := by
    rw [hmx, hrun]
    congr 1 <;> omega
  conv_rhs => rw [decompA hA]
  rw [op2, hfilter, hIccEq, hrun]

end ASide

section BSide

variable {t : Finset ℕ}

