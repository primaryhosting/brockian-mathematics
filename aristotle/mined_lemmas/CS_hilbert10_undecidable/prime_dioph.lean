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

theorem prime_dioph {α : Type} {f : (α → ℕ) → ℕ} (df : DiophFn f) :
    Dioph {v | Nat.Prime (f v)} := by
  have h1 : Dioph {v : α → ℕ | 1 < f v} := Dioph.lt_dioph (Dioph.const_dioph 1) df
  have h2 : Dioph {v : α → ℕ | f v ∣ ((f v - 1)! + 1)} :=
    Dioph.dvd_dioph df
      (Dioph.add_dioph (factorial_dioph (Dioph.sub_dioph df (Dioph.const_dioph 1)))
        (Dioph.const_dioph 1))
  refine Dioph.ext (Dioph.inter h1 h2) fun v => ?_
  simpa using (prime_iff_dvd_factorial (f v)).symm

/-! ### Coding of finite sequences -/

/-- Gödel-style coding of a finite sequence: if the modulus base `b` is divisible by `n !`
(which makes the moduli `1 + (i+1) * b` pairwise coprime) and dominates the entries, then a
single number `a` codes the sequence via `a % (1 + (i+1) * b)`. -/
