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

theorem exists_beta (s : ℕ → ℕ) (x : ℕ) : ∃ c d, ∀ i ≤ x, beta c d i = s i := by
  classical
  set M : ℕ := max x ((Finset.range (x + 1)).sup s) with hM
  set b : ℕ := M ! with hb
  have hMb : M ≤ b := Nat.self_le_factorial _
  have hxfac : (x)! ∣ b := Nat.factorial_dvd_factorial (le_max_left _ _)
  have hlt : ∀ i ≤ x, s i < 1 + (i + 1) * b := by
    intro i hi
    have h1 : s i ≤ M := le_trans (Finset.le_sup (f := s) (Finset.mem_range.2 (by omega)))
      (le_max_right _ _)
    have h2 : b ≤ (i + 1) * b := Nat.le_mul_of_pos_left _ (by omega)
    omega
  obtain ⟨c, hc⟩ := exists_crt_code s x b hxfac hlt
  exact ⟨c, b, fun i hi => hc i hi⟩

