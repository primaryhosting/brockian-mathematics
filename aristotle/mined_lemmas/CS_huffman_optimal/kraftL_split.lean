import Mathlib

/-!
# Kraft's inequality

This file proves the Kraft inequality for finite prefix-free binary codes.
It is part of the development of `CS.huffman_optimal`.
-/

namespace CS

open List

/-- A list of binary codewords is prefix-free when no codeword is a prefix of another. -/

lemma kraftL_split {L : List (List Bool)} (h : ∀ s ∈ L, s ≠ []) :
    kraftL L = (kraftL (child false L) + kraftL (child true L)) / 2 := by
  induction L with
  | nil => simp [kraftL, child]
  | cons s L ih =>
    have hL : ∀ t ∈ L, t ≠ [] := fun t ht => h t (List.mem_cons_of_mem _ ht)
    have ihL := ih hL
    match s with
    | [] => exact absurd rfl (h [] (List.mem_cons_self ..))
    | c :: t =>
      cases c with
      | false =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (false = true))]
        simp only [kraftL, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        rw [ihL]; ring
      | true =>
        simp only [child, if_pos rfl, if_neg (by simp : ¬ (true = false))]
        simp only [kraftL, List.map_cons, List.sum_cons, List.length_cons] at ihL ⊢
        rw [ihL]; ring

