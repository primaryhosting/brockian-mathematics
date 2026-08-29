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

private lemma decompA (hA : IsA s) :
    s = insert (mn s) ((s.erase (mn s)).filter (fun x => x ≤ mx s - mn s)
      ∪ Finset.Icc (mx s - mn s + 1) (mx s)) := by
  obtain ⟨hs, hle, -⟩ := hA
  ext x
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_erase,
    Finset.mem_Icc]
  constructor
  · intro hx
    by_cases hxa : x = mn s
    · exact Or.inl hxa
    · refine Or.inr ?_
      by_cases hcase : x ≤ mx s - mn s
      · exact Or.inl ⟨⟨hxa, hx⟩, hcase⟩
      · exact Or.inr ⟨by omega, le_mx hx⟩
  · rintro (rfl | ⟨⟨-, hx⟩, -⟩ | ⟨h1, h2⟩)
    · exact mn_mem hs
    · exact hx
    · exact Icc_run_subset hs (Finset.mem_Icc.mpr ⟨by omega, h2⟩)

section ASide

variable {s : Finset ℕ}

