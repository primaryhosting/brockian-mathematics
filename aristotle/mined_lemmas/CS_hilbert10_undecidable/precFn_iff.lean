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

theorem precFn_iff {n : ℕ} (F : Vector3 ℕ n → ℕ) (G : Vector3 ℕ (n + 2) → ℕ)
    (w : Vector3 ℕ n) (x z : ℕ) :
    precFn F G w x = z ↔ ∃ c d, beta c d 0 = F w ∧
      (∀ i < x, beta c d (i + 1) = G (Vector3.cons i (Vector3.cons (beta c d i) w))) ∧
      beta c d x = z := by
  constructor
  · rintro rfl
    obtain ⟨c, d, hcd⟩ := exists_beta (precFn F G w) x
    refine ⟨c, d, ?_, ?_, hcd x le_rfl⟩
    · rw [hcd 0 (Nat.zero_le _)]; rfl
    · intro i hi
      rw [hcd (i + 1) (by omega), hcd i (by omega)]
      rfl
  · rintro ⟨c, d, h0, hstep, hx⟩
    have key : ∀ i ≤ x, beta c d i = precFn F G w i := by
      intro i
      induction i with
      | zero => intro _; exact h0
      | succ i ih =>
          intro hi
          rw [hstep i (by omega), ih (by omega)]
          rfl
    rw [← hx, key x le_rfl]

/-- Primitive recursion preserves Diophantine functions. -/
