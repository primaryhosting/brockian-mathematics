/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem nadd_lt_opow_succ (δ : Ordinal)
    (IH : ∀ x y : Ordinal, x < ω ^ δ → y < ω ^ δ → x ♯ y < ω ^ δ) :
    ∀ a b : Ordinal, a < ω ^ (δ + 1) → b < ω ^ (δ + 1) → a ♯ b < ω ^ (δ + 1) := by
  have hP : (ω : Ordinal) ^ δ ≠ 0 := (Ordinal.opow_pos δ omega0_pos).ne'
  intro a b ha hb
  rw [Ordinal.opow_add, Ordinal.opow_one] at ha hb ⊢
  set P : Ordinal := ω ^ δ with hPdef
  have hqa : a / P < ω := (Ordinal.div_lt hP).2 ha
  have hqb : b / P < ω := (Ordinal.div_lt hP).2 hb
  have hra : a % P < P := Ordinal.mod_lt a hP
  have hrb : b % P < P := Ordinal.mod_lt b hP
  have hmain := nadd_le_div_mod δ IH a b ha hb
  have h1 : P * (a / P + b / P) + (a % P ♯ b % P) < P * (a / P + b / P + 1) := by
    rw [mul_add_one]
    exact add_lt_add_right (IH _ _ hra hrb) _
  have h2 : P * (a / P + b / P + 1) < P * ω := by
    refine (mul_lt_mul_iff_of_pos_left (Ordinal.opow_pos δ omega0_pos)).2 ?_
    obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
    obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
    rw [hna, hnb, ← Nat.cast_add, ← Nat.cast_one, ← Nat.cast_add]
    exact Ordinal.nat_lt_omega0 (na + nb + 1)
  exact lt_of_le_of_lt hmain (h1.trans h2)

/-- **Additive principality of `ω ^ γ`**: the set of ordinals below `ω ^ γ` is closed
under the natural (Hessenberg) sum. -/
