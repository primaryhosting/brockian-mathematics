import RequestProject.Huffman

/-!
# Achievability of the Huffman cost

Companion to `RequestProject.Huffman`.  Here we show that the Huffman cost is *attained*:
there really is a prefix code whose expected codeword length equals `CS.huffCost`.

Combined with the optimality bound `CS.huffman_optimal`, this gives
`CS.huffman_isLeast`: the Huffman cost is the least expected codeword length among all
prefix codes.
-/

namespace CS

open scoped BigOperators

noncomputable section

/-- A multiset of binary codewords is prefix-free: the codewords are pairwise distinct and
none is a prefix of another. -/

theorem exists_fun_of_map_eq {α β γ : Type*} [DecidableEq α] [Nonempty β] (f : β → γ)
    (g : α → γ) : ∀ (s : Finset α) (S : Multiset β), S.map f = s.val.map g →
      ∃ h : α → β, s.val.map h = S ∧ ∀ a ∈ s, f (h a) = g a := by
  intro s
  induction s using Finset.cons_induction with
  | empty =>
      intro S hS
      refine ⟨fun _ => Classical.arbitrary β, ?_, by simp⟩
      simp only [Finset.empty_val, Multiset.map_zero] at hS ⊢
      exact (Multiset.map_eq_zero.1 hS).symm
  | cons a s ha ih =>
      intro S hS
      rw [Finset.cons_val, Multiset.map_cons] at hS
      have hga : g a ∈ S.map f := by rw [hS]; exact Multiset.mem_cons_self _ _
      obtain ⟨b, hbS, hb⟩ := Multiset.mem_map.1 hga
      obtain ⟨S₀, hS₀⟩ := Multiset.exists_cons_of_mem hbS
      have hS₀map : S₀.map f = s.val.map g := by
        rw [hS₀, Multiset.map_cons, hb] at hS
        exact (Multiset.cons_inj_right _).1 hS
      obtain ⟨h', hh'1, hh'2⟩ := ih S₀ hS₀map
      refine ⟨Function.update h' a b, ?_, ?_⟩
      · rw [Finset.cons_val, Multiset.map_cons, hS₀]
        congr 1
        · simp
        · rw [← hh'1]
          refine Multiset.map_congr rfl ?_
          intro x hx
          have : x ≠ a := by rintro rfl; exact ha hx
          simp [Function.update_of_ne this]
      · intro c hc
        rcases Finset.mem_cons.1 hc with rfl | hc'
        · simpa using hb
        · have hca : c ≠ a := by rintro rfl; exact ha hc'
          rw [Function.update_of_ne hca]
          exact hh'2 c hc'

/-- **Achievability**: for any finite alphabet with weights there is a prefix code whose
expected codeword length is exactly the Huffman cost. -/
