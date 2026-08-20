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

theorem prefixFree_split (v : List Bool) (V : Multiset (List Bool))
    (h : PrefixFreeMultiset (v ::ₘ V)) :
    PrefixFreeMultiset ((v ++ [false]) ::ₘ (v ++ [true]) ::ₘ V) := by
  obtain ⟨hnd, hpf⟩ := h
  rw [Multiset.nodup_cons] at hnd
  obtain ⟨hvV, hVnd⟩ := hnd
  have hA : ∀ u ∈ V, ¬ (v <+: u) ∧ ¬ (u <+: v) := by
    intro u hu
    have hne : u ≠ v := by rintro rfl; exact hvV hu
    exact ⟨hpf v (Multiset.mem_cons_self _ _) u (Multiset.mem_cons_of_mem hu) (Ne.symm hne),
      hpf u (Multiset.mem_cons_of_mem hu) v (Multiset.mem_cons_self _ _) hne⟩
  have hB : ∀ b : Bool, v ++ [b] ∉ V := by
    intro b hb
    exact (hA _ hb).1 ⟨[b], rfl⟩
  have hne01 : v ++ [false] ≠ v ++ [true] := by simp
  have hkey : ∀ b : Bool, ∀ u ∈ V, ¬ (v ++ [b] <+: u) ∧ ¬ (u <+: v ++ [b]) := by
    intro b u hu
    refine ⟨fun hp => (hA u hu).1 (List.IsPrefix.trans ⟨[b], rfl⟩ hp), fun hp => ?_⟩
    rcases List.prefix_concat_iff.mp hp with h1 | h1
    · exact hB b (h1 ▸ hu)
    · exact (hA u hu).2 h1
  refine ⟨?_, ?_⟩
  · rw [Multiset.nodup_cons, Multiset.nodup_cons]
    refine ⟨?_, hB true, hVnd⟩
    simp only [Multiset.mem_cons]
    push_neg
    exact ⟨hne01, hB false⟩
  · intro u hu w hw hne hpre
    simp only [Multiset.mem_cons] at hu hw
    rcases hu with rfl | rfl | hu
    · rcases hw with rfl | rfl | hw
      · exact hne rfl
      · rw [List.prefix_append_right_inj] at hpre; simp at hpre
      · exact (hkey false w hw).1 hpre
    · rcases hw with rfl | rfl | hw
      · rw [List.prefix_append_right_inj] at hpre; simp at hpre
      · exact hne rfl
      · exact (hkey true w hw).1 hpre
    · rcases hw with rfl | rfl | hw
      · exact (hkey false u hu).2 hpre
      · exact (hkey true u hu).2 hpre
      · exact hpf u (Multiset.mem_cons_of_mem hu) w (Multiset.mem_cons_of_mem hw) hne hpre

/-- The Huffman cost of a multiset of weights is attained by an actual prefix-free code. -/
