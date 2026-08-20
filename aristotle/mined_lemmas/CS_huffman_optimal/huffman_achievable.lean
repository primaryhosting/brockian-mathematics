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

theorem huffman_achievable {α : Type*} [Fintype α] (w : α → ℝ) :
    ∃ c : α → List Bool, IsPrefixCode c ∧
      ∑ a, w a * ((c a).length : ℝ) = huffCost (Multiset.map w Finset.univ.val) := by
  classical
  obtain ⟨S, hfst, hpf, hcost⟩ :=
    huffCost_achievable_aux _ (Multiset.map w Finset.univ.val) rfl
  obtain ⟨h, hh1, hh2⟩ :=
    exists_fun_of_map_eq (β := ℝ × List Bool) Prod.fst w Finset.univ S hfst
  refine ⟨fun a => (h a).2, ?_, ?_⟩
  · -- prefix code
    have hsnd : S.map Prod.snd = Multiset.map (fun a => (h a).2) Finset.univ.val := by
      rw [← hh1, Multiset.map_map]
      rfl
    have hinj : Function.Injective (fun a => (h a).2) := by
      have hnd := hpf.1
      rw [hsnd, Multiset.nodup_map_iff_inj_on Finset.univ.nodup] at hnd
      intro a b hab
      exact hnd a (Finset.mem_univ a) b (Finset.mem_univ b) hab
    intro a b hab hpre
    refine hpf.2 ((h a).2) ?_ ((h b).2) ?_ (fun heq => hab (hinj heq)) hpre
    · rw [hsnd]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ a)
    · rw [hsnd]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ b)
  · rw [← hcost, codeCost, ← hh1, Multiset.map_map, ← Finset.sum_map_val]
    refine Finset.sum_congr rfl ?_
    intro a _
    simp only [Function.comp_apply]
    rw [hh2 a (Finset.mem_univ a)]

/-- **Huffman coding minimizes the expected codeword length among prefix codes**: the
Huffman cost is the least element of the set of expected codeword lengths of prefix codes
over a finite alphabet with nonnegative weights. -/
