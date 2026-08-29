import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/

lemma mem_child (b : Bool) {L : List (List Bool)} {u : List Bool}
    (hu : u ∈ child b L) : (b :: u) ∈ L := by
  induction L with
  | nil => simp [child] at hu
  | cons s L ih =>
    match s with
    | [] =>
      simp only [child] at hu
      exact List.mem_cons_of_mem _ (ih hu)
    | c :: t =>
      simp only [child] at hu
      by_cases hcb : c = b
      · subst hcb
        simp only [if_pos rfl, List.mem_cons] at hu
        rcases hu with h | h
        · subst h; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (ih h)
      · rw [if_neg hcb] at hu
        exact List.mem_cons_of_mem _ (ih hu)

