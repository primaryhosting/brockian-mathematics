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

theorem exists_int_iff_exists_nat {m : ℕ} (P : MvPolynomial (Fin (m + 1)) ℤ) (a : ℤ) :
    (∃ y : Fin (m * 4) → ℤ, eval (Fin.cons a y) (bind₁ fourSq P) = 0) ↔
      ∃ x : Fin m → ℕ, eval (Fin.cons a fun i => (x i : ℤ)) P = 0 := by
  classical
  constructor
  · rintro ⟨y, hy⟩
    rw [eval_bind_fourSq] at hy
    refine ⟨fun i => (∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2).toNat, ?_⟩
    have hcast : ∀ i : Fin m,
        (((∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2).toNat : ℤ))
          = ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2 := fun i =>
      Int.toNat_of_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
    rw [show (fun i : Fin m => (((∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2).toNat : ℤ)))
        = fun i => ∑ k : Fin 4, (y (finProdFinEquiv (i, k))) ^ 2 from funext hcast]
    exact hy
  · rintro ⟨x, hx⟩
    choose A B C D hABCD using fun i : Fin m => Nat.sum_four_squares (x i)
    refine ⟨fun j => ((![A ((finProdFinEquiv.symm j).1), B ((finProdFinEquiv.symm j).1),
      C ((finProdFinEquiv.symm j).1), D ((finProdFinEquiv.symm j).1)]
        ((finProdFinEquiv.symm j).2) : ℕ) : ℤ), ?_⟩
    rw [eval_bind_fourSq]
    have hsum : ∀ i : Fin m,
        (∑ k : Fin 4, (((![A i, B i, C i, D i] k : ℕ) : ℤ)) ^ 2) = (x i : ℤ) := by
      intro i
      rw [Fin.sum_univ_four]
      have h := hABCD i
      push_cast [← h]
      ring
    rw [show (fun i : Fin m => ∑ k : Fin 4,
        (((![A ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1),
            B ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1),
            C ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1),
            D ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).1)]
          ((finProdFinEquiv.symm (finProdFinEquiv (i, k))).2) : ℕ) : ℤ)) ^ 2)
        = fun i : Fin m => (x i : ℤ) from funext (fun i => by
          simp only [Equiv.symm_apply_apply]
          exact hsum i)]
    exact hx

/-- **Hilbert's tenth problem is undecidable, for solutions in the integers.**  There is a
polynomial `Q` with integer coefficients such that no algorithm decides, for a given natural
number `a`, whether `Q (a, y₁, …, yₙ) = 0` has a solution in integers. -/
