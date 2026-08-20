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

theorem progProd_lt (y b : ℕ) (hb : 0 < b) : progProd y b < b * (1 + y * b) ^ (y + 1) + 1 := by
  have h1 : progProd y b ≤ (1 + y * b) ^ y := by
    unfold progProd
    calc ∏ k ∈ Finset.range y, (1 + (k + 1) * b) ≤ ∏ _k ∈ Finset.range y, (1 + y * b) := by
          refine Finset.prod_le_prod' ?_
          intro i hi
          simp only [Finset.mem_range] at hi
          have : (i + 1) * b ≤ y * b := Nat.mul_le_mul_right _ (by omega)
          omega
      _ = (1 + y * b) ^ y := by simp
  have h2 : (1 + y * b) ^ y ≤ b * (1 + y * b) ^ (y + 1) :=
    le_trans (Nat.pow_le_pow_right (by omega) (by omega)) (Nat.le_mul_of_pos_left _ hb)
  omega

/-- The key congruence making `progProd` Diophantine: modulo a suitable large modulus, the
product of the arithmetic progression is a power times a descending factorial. -/
