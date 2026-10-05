import Mathlib

/-!
# Kraft's inequality for prefix-free codes
-/

namespace CS

open scoped BigOperators


theorem exists_pair_of_map_fst {β : Type*} {M : Multiset (β × ℕ)} {b : β} {s : Multiset β}
    (h : M.map Prod.fst = b ::ₘ s) :
    ∃ (k : ℕ) (M' : Multiset (β × ℕ)), M = (b, k) ::ₘ M' ∧ M'.map Prod.fst = s := by
  have hb : b ∈ M.map Prod.fst := by rw [h]; exact Multiset.mem_cons_self _ _
  rw [Multiset.mem_map] at hb
  obtain ⟨p, hp, hpb⟩ := hb
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hp
  refine ⟨p.2, M', ?_, ?_⟩
  · rw [hM']
    congr 1
    exact Prod.ext hpb rfl
  · rw [hM', Multiset.map_cons, hpb] at h
    exact (Multiset.cons_inj_right b).1 h

/-- **Optimality of Huffman's algorithm.**  For any Kraft-admissible assignment of codeword
lengths to the trees of `ts`, the tree produced by Huffman's algorithm costs no more. -/
