import RequestProject.HuffmanKraft

/-!
# Weighted depth multisets, the Huffman merging process, and the optimality bound
-/

namespace CS

/-- A *weighted depth multiset*: a finite multiset of pairs `(weight, codeword length)`. -/
abbrev WD := Multiset (ℝ × ℕ)

/-- The expected codeword length associated to a weighted depth multiset. -/

theorem kn_parity (M : ℕ) (D : WD) (h : ∀ p ∈ D, p.2 ≤ M) :
    ∃ t : ℕ, kn M D = D.countP (fun p => p.2 = M) + 2 * t := by
  classical
  induction D using Multiset.induction with
  | empty => exact ⟨0, by simp⟩
  | cons a D ih =>
    obtain ⟨t, ht⟩ := ih fun p hp => h p (Multiset.mem_cons_of_mem hp)
    have ha : a.2 ≤ M := h a (Multiset.mem_cons_self _ _)
    rw [Multiset.countP_cons, kn_cons, ht]
    by_cases hd : a.2 = M
    · refine ⟨t, ?_⟩
      simp [hd]
      omega
    · have h1 : 1 ≤ M - a.2 := by omega
      obtain ⟨k, hk⟩ : ∃ k, M - a.2 = k + 1 := ⟨M - a.2 - 1, by omega⟩
      refine ⟨2 ^ k + t, ?_⟩
      simp only [hd, if_false, hk, pow_succ]
      ring_nf

/-- From a multiset with at least two elements satisfying `P`, extract two such elements. -/
