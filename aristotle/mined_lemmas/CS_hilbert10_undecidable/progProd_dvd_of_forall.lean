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

theorem progProd_dvd_of_forall {b N : ℕ} : ∀ {y : ℕ}, (∀ d, 0 < d → d ≤ y → d ∣ b) →
    (∀ k < y, 1 + (k + 1) * b ∣ N) → progProd y b ∣ N := by
  intro y
  induction y with
  | zero => intro _ _; simp [progProd]
  | succ y ih =>
      intro hb h
      have hco : Nat.Coprime (progProd y b) (1 + (y + 1) * b) := by
        refine Nat.Coprime.prod_left ?_
        intro k hk
        simp only [Finset.mem_range] at hk
        have hd : (y + 1) - (k + 1) ∣ b := hb _ (by omega) (by omega)
        simpa [Nat.add_comm] using Nat.coprime_mul_succ hd
      have h1 : progProd y b ∣ N :=
        ih (fun d hd hdy => hb d hd (by omega)) (fun k hk => h k (by omega))
      have h2 : 1 + (y + 1) * b ∣ N := h y (by omega)
      have hsplit : progProd (y + 1) b = progProd y b * (1 + (y + 1) * b) := by
        simp [progProd, Finset.prod_range_succ]
      rw [hsplit]
      exact hco.mul_dvd_of_dvd_of_dvd h1 h2

/-! ### Finitely many Diophantine conditions -/

/-- A finite family of Diophantine conditions is Diophantine. -/
