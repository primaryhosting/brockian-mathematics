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

theorem factorial_bound (n : ℕ) : n ^ 2 * ((n)! + 1) < (n + 1) ^ (n + 3) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 : (n)! + 1 ≤ (n + 1) ^ n := by
    have ha : (n)! ≤ n ^ n := Nat.factorial_le_pow n
    have hb : n ^ n < (n + 1) ^ n := Nat.pow_lt_pow_left (by omega) (by omega)
    omega
  have h2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  calc n ^ 2 * ((n)! + 1) ≤ (n + 1) ^ 2 * (n + 1) ^ n := Nat.mul_le_mul h2 h1
    _ = (n + 1) ^ (n + 2) := by rw [← pow_add]; congr 1; omega
    _ < (n + 1) ^ (n + 3) := Nat.pow_lt_pow_right (by omega) (by omega)

/-- Closed arithmetic formula for the factorial. -/
