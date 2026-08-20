import RequestProject.DiophAux

/-!
# Davis' bounded universal quantifier

This file proves that bounded universal quantification preserves Diophantine sets:
if `S` is Diophantine, so is `{v | ∀ x < f v, (x, v) ∈ S}`.
-/

open Dioph Nat Sum

namespace CS

variable {α : Type} {n : ℕ}

/-- The bound `B` used in Davis' construction: it dominates the value of the majorant `q`
at the extreme arguments, as well as `y` and `u`. -/

theorem eval_bind_fourSq {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ) (a : ℤ)
    (y : Fin (m * 4) → ℤ) :
    eval (Fin.cons a y) (bind₁ fourSq P)
      = eval (Fin.cons a (fun i => ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2)) P := by
  rw [show eval (Fin.cons a y) (bind₁ fourSq P)
      = eval (fun i => eval (Fin.cons a y) (fourSq i)) P from
    MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℤ) (Fin.cons a y) fourSq P]
  have hfun : (fun i => eval (Fin.cons a y) (fourSq i))
      = Fin.cons a (fun i => ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp [fourSq]
    · intro j
      simp [fourSq]
  rw [hfun]

/-- **Lagrange's trick.**  Solvability in natural numbers is equivalent to solvability in
integers once each unknown is replaced by a sum of four squares. -/
