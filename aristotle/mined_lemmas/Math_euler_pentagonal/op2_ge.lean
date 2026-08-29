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

lemma op2_ge (h0 : 0 ∉ t) (hB : IsB t) {x : ℕ} (hx : x ∈ op2 t) : run t ≤ x := by
  have h2 := IsB.two_run_lt_mx h0 hB
  rw [op2_eq] at hx
  simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc] at hx
  rcases hx with rfl | ⟨hmem, -⟩ | ⟨h1, -⟩
  · exact le_refl _
  · exact le_of_lt (lt_of_lt_of_le hB.2.1 (mn_le hB.1 hmem))
  · omega

