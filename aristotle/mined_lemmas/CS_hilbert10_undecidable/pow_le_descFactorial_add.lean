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

theorem pow_le_descFactorial_add (r : ℕ) : ∀ n, n ≤ r →
    r ^ n ≤ r.descFactorial n + n ^ 2 * r ^ (n - 1) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
      intro hn
      have hn' : n ≤ r := by omega
      have h1 := ih hn'
      have hDle : r.descFactorial n ≤ r ^ n := Nat.descFactorial_le_pow r n
      have hkey : r ^ n * r ≤ (r.descFactorial n + n ^ 2 * r ^ (n - 1)) * r :=
        Nat.mul_le_mul_right _ h1
      have hpow : n ^ 2 * r ^ (n - 1) * r = n ^ 2 * r ^ n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · simp [h]
        · rw [mul_assoc]
          congr 1
          rw [← pow_succ]
          congr 1
          omega
      have hsplit : r.descFactorial n * r = r.descFactorial (n + 1) + n * r.descFactorial n := by
        rw [Nat.descFactorial_succ r n]
        have hr : r = (r - n) + n := by omega
        calc r.descFactorial n * r = r.descFactorial n * ((r - n) + n) := by rw [← hr]
          _ = (r - n) * r.descFactorial n + n * r.descFactorial n := by ring
      calc r ^ (n + 1) = r ^ n * r := by ring
        _ ≤ (r.descFactorial n + n ^ 2 * r ^ (n - 1)) * r := hkey
        _ = r.descFactorial n * r + n ^ 2 * r ^ (n - 1) * r := by ring
        _ = r.descFactorial (n + 1) + n * r.descFactorial n + n ^ 2 * r ^ n := by
              rw [hsplit, hpow]
        _ ≤ r.descFactorial (n + 1) + n * r ^ n + n ^ 2 * r ^ n := by gcongr
        _ ≤ r.descFactorial (n + 1) + (n + 1) ^ 2 * r ^ ((n + 1) - 1) := by
              simp only [Nat.add_sub_cancel]
              nlinarith [Nat.zero_le (r ^ n)]

/-- For sufficiently large `r`, the factorial is a quotient of a power by a binomial
coefficient. -/
