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

theorem exists_progProd_witness (y b : ℕ) (hb : 0 < b) :
    ∃ m, y ≤ m ∧ b * m ≡ 1 + y * b [MOD (b * (1 + y * b) ^ (y + 1) + 1)] := by
  set M := b * (1 + y * b) ^ (y + 1) + 1 with hM
  have hM1 : 1 < M := by
    have h1 : 1 ≤ (1 + y * b) ^ (y + 1) := Nat.one_le_pow _ _ (by omega)
    have h2 : b ≤ b * (1 + y * b) ^ (y + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hcop : Nat.Coprime b M := by rw [hM]; simp
  obtain ⟨m₀, _, hm₀⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hM1
  refine ⟨m₀ * (1 + y * b) + M * y, ?_, ?_⟩
  · have : y ≤ M * y := Nat.le_mul_of_pos_left _ (by omega)
    omega
  · have h1 : b * m₀ ≡ 1 [MOD M] := by
      unfold Nat.ModEq
      rw [hm₀, Nat.one_mod_eq_one.mpr (by omega)]
    calc b * (m₀ * (1 + y * b) + M * y) = (b * m₀) * (1 + y * b) + M * (b * y) := by ring
      _ ≡ 1 * (1 + y * b) + M * (b * y) [MOD M] := Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ h1)
      _ = (1 + y * b) + M * (b * y) := by ring
      _ ≡ (1 + y * b) + 0 [MOD M] := Nat.ModEq.add_left _ (Nat.modEq_zero_iff_dvd.mpr ⟨b * y, rfl⟩)
      _ = 1 + y * b := by ring

/-- Products of arithmetic progressions are Diophantine (Davis' lemma). -/
