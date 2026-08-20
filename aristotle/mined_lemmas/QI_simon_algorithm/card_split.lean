/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

lemma card_split {n : ℕ} (S : Finset (Bits n)) (t y0 : Bits n)
    (hS : ∀ y : Bits n, y ∈ S ↔ y + y0 ∈ S) (h0 : bdot y0 t = 1) :
    2 * (S.filter (fun y => bdot y t = 0)).card = S.card := by
  classical
  have hpart : (S.filter (fun y => bdot y t = 0)).card
      + (S.filter (fun y => ¬ bdot y t = 0)).card = S.card :=
    Finset.card_filter_add_card_filter_not _
  have hcard : (S.filter (fun y => ¬ bdot y t = 0)).card
      = (S.filter (fun y => bdot y t = 0)).card := by
    refine Finset.card_bij' (fun y _ => y + y0) (fun y _ => y + y0) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      refine ⟨(hS y).1 hy.1, ?_⟩
      rw [bdot_add_left, h0]
      rcases zmod_two_cases (bdot y t) with h | h
      · exact absurd h hy.2
      · rw [h]; decide
    · intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      refine ⟨(hS y).1 hy.1, ?_⟩
      rw [bdot_add_left, h0, hy.2]
      decide
    · intro y _
      simp only [add_assoc, bits_add_self, add_zero]
    · intro y _
      simp only [add_assoc, bits_add_self, add_zero]
  omega

/-- The set of bit strings orthogonal to `s`. -/
