import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem ival_mid_not_dvd : ∀ (n : ℕ) (L : List (Fin 2 × Bool)), L.length = n →
    FreeGroup.IsReduced L → L ≠ [] → ¬ ((3 : ℤ) ∣ (ival L).2.1) := by
  intro n
  induction n with
  | zero => intro L hL _ hne; exact absurd (List.length_eq_zero_iff.mp hL) hne
  | succ m ih =>
    intro L hL hred hne
    match L with
    | [x] =>
      rcases x with ⟨i, b⟩
      fin_cases i <;> cases b <;> simp [ival, istep]
    | x :: y :: t =>
      have hIH := ih (y :: t) (by simpa using hL) (FreeGroup.isReduced_cons_cons.mp hred).2
        (by simp)
      have hxy := (FreeGroup.isReduced_cons_cons.mp hred).1
      rcases x with ⟨i, b⟩; rcases y with ⟨j, c⟩
      simp only [ival] at hIH ⊢
      fin_cases i <;> fin_cases j <;> cases b <;> cases c <;>
        simp [istep] at hxy hIH ⊢ <;> omega

/-! ### The real computation -/

/-- The matrix of a letter. -/
