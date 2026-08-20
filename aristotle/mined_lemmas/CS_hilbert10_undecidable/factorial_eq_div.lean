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

theorem factorial_eq_div (n r : ℕ) (hr : n ^ 2 * ((n)! + 1) < r) :
    (n)! = r ^ n / r.choose n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnr : n ≤ r := by nlinarith [Nat.factorial_pos n, sq_nonneg n]
  have hr0 : 0 < r := by omega
  have hD : r.descFactorial n = (n)! * r.choose n := Nat.descFactorial_eq_factorial_mul_choose r n
  have h1 : (n)! * r.choose n ≤ r ^ n := by
    rw [← hD]; exact Nat.descFactorial_le_pow r n
  have h2 : r ^ n ≤ r.descFactorial n + n ^ 2 * r ^ (n - 1) := pow_le_descFactorial_add r n hnr
  have hpow : r ^ n = r * r ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hp : 0 < r ^ (n - 1) := Nat.pow_pos hr0
  have hstrict : ((n)! + 1) * (n ^ 2 * r ^ (n - 1)) < r ^ n := by
    rw [hpow]
    calc ((n)! + 1) * (n ^ 2 * r ^ (n - 1)) = (n ^ 2 * ((n)! + 1)) * r ^ (n - 1) := by ring
      _ < r * r ^ (n - 1) := Nat.mul_lt_mul_of_lt_of_le hr (le_refl _) hp
  have hkey : n ^ 2 * r ^ (n - 1) < r.choose n := by
    have hlt : (n)! * (n ^ 2 * r ^ (n - 1)) < (n)! * r.choose n := by
      have hsum : (n)! * (n ^ 2 * r ^ (n - 1)) + n ^ 2 * r ^ (n - 1) < r ^ n := by
        calc (n)! * (n ^ 2 * r ^ (n - 1)) + n ^ 2 * r ^ (n - 1)
            = ((n)! + 1) * (n ^ 2 * r ^ (n - 1)) := by ring
          _ < r ^ n := hstrict
      omega
    exact Nat.lt_of_mul_lt_mul_left hlt
  refine (Nat.div_eq_of_lt_le h1 ?_).symm
  calc r ^ n ≤ r.descFactorial n + n ^ 2 * r ^ (n - 1) := h2
    _ = (n)! * r.choose n + n ^ 2 * r ^ (n - 1) := by rw [hD]
    _ < (n)! * r.choose n + r.choose n := by omega
    _ = ((n)! + 1) * r.choose n := by ring

/-- An explicit admissible choice of the parameter `r` in `CS.factorial_eq_div`. -/
