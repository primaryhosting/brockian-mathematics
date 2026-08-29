import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/

lemma prefixFree_child (b : Bool) {L : List (List Bool)} (h : PrefixFreeList L) :
    PrefixFreeList (child b L) := by
  induction L with
  | nil => simp [child, PrefixFreeList]
  | cons s L ih =>
    rw [PrefixFreeList, List.pairwise_cons] at h
    obtain ⟨hhead, htail⟩ := h
    have ihp := ih htail
    match s with
    | [] => simpa only [child] using ihp
    | c :: t =>
      simp only [child]
      by_cases hcb : c = b
      · subst hcb
        rw [if_pos rfl, PrefixFreeList, List.pairwise_cons]
        refine ⟨?_, ihp⟩
        intro u hu
        have hmem := mem_child c hu
        have := hhead _ hmem
        constructor
        · intro hpre
          exact this.1 (List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
        · intro hpre
          exact this.2 (List.cons_prefix_cons.2 ⟨rfl, hpre⟩)
      · rw [if_neg hcb]; exact ihp

