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

lemma sum_sgn {n : ℕ} (w : Bits n) :
    ∑ x : Bits n, sgn x w = if w = 0 then (2:ℂ) ^ n else 0 := by
  classical
  by_cases hw : w = 0
  · subst hw
    simp [sgn, Finset.card_univ]
  · rw [if_neg hw]
    simp only [sgn]
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hfil : (Finset.univ.filter (fun x : Bits n => bdot x w = 0)) = orth w := rfl
    have hsplit : (Finset.univ.filter (fun x : Bits n => bdot x w = 0)).card
        + (Finset.univ.filter (fun x : Bits n => ¬ bdot x w = 0)).card
        = (Finset.univ : Finset (Bits n)).card :=
      Finset.card_filter_add_card_filter_not _
    have huniv : (Finset.univ : Finset (Bits n)).card = 2 ^ n := by simp
    have h2 : 2 * (orth w).card = 2 ^ n := card_orth w hw
    rw [hfil] at hsplit
    have heq : (Finset.univ.filter (fun x : Bits n => ¬ bdot x w = 0)).card = (orth w).card := by
      omega
    rw [hfil, heq]
    ring

/-- Orthogonality of the characters `x ↦ (-1)^⟨x,y⟩`. -/
