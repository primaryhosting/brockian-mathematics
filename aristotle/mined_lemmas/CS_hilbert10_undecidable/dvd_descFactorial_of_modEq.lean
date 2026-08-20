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

theorem dvd_descFactorial_of_modEq {a x u m : ℕ} (h : a ≡ x [MOD m]) (hxu : x ≤ u) :
    m ∣ a.descFactorial (u + 1) := by
  rcases lt_or_ge a x with hax | hax
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 (show a < u + 1 by omega)]
    exact dvd_zero m
  · rw [Nat.descFactorial_eq_prod_range]
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => a - i)
      (Finset.mem_range.2 (show x < u + 1 by omega)))
    exact (Nat.modEq_iff_dvd' hax).mp h.symm

/-- Conversely, if a prime `P > u` divides `a (a-1) ⋯ (a-u)` then the residue of `a` mod `P`
is at most `u`. -/
