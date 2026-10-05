import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/

lemma lenSum_split {L : List (List Bool)} (h : ∀ s ∈ L, s ≠ []) :
    lenSum L = L.length + lenSum (child false L) + lenSum (child true L) := by
  induction L with
  | nil => simp [lenSum, child]
  | cons s L ih =>
    have hL : ∀ t ∈ L, t ≠ [] := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have ihL := ih hL
    match s with
    | [] => exact absurd rfl (h [] (List.mem_cons_self ..))
    | c :: t =>
      cases c with
      | false =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (false = true))]
        simp only [lenSum, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        omega
      | true =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (true = false))]
        simp only [lenSum, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        omega

/-- **Kraft's inequality**: a finite prefix-free binary code satisfies `∑ 2^(-|s|) ≤ 1`. -/
