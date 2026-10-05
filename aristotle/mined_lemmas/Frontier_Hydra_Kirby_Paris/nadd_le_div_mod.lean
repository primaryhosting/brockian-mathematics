/-
Auxiliary ordinal arithmetic: additive principality of `ω ^ γ` for the natural
(Hessenberg) sum `♯`.
-/
import Mathlib

open Ordinal NaturalOps Order

namespace Frontier

/-- Comparing two ordinals through their quotient and remainder by `P`. -/

theorem nadd_le_div_mod (δ : Ordinal)
    (IH : ∀ x y : Ordinal, x < ω ^ δ → y < ω ^ δ → x ♯ y < ω ^ δ) :
    ∀ a b : Ordinal, a < ω ^ δ * ω → b < ω ^ δ * ω →
      a ♯ b ≤ ω ^ δ * (a / ω ^ δ + b / ω ^ δ) + (a % ω ^ δ ♯ b % ω ^ δ) := by
  have hP : (ω : Ordinal) ^ δ ≠ 0 := (Ordinal.opow_pos δ omega0_pos).ne'
  intro a
  induction a using Ordinal.induction with
  | _ a IHa =>
    intro b
    induction b using Ordinal.induction with
    | _ b IHb =>
      intro ha hb
      set P : Ordinal := ω ^ δ with hPdef
      have hqa : a / P < ω := (Ordinal.div_lt hP).2 ha
      have hqb : b / P < ω := (Ordinal.div_lt hP).2 hb
      have hra : a % P < P := Ordinal.mod_lt a hP
      have hrb : b % P < P := Ordinal.mod_lt b hP
      rw [nadd_le_iff]
      constructor
      · intro a' ha'
        have ha'ω : a' < P * ω := ha'.trans ha
        have hstep := IHa a' ha' b ha'ω hb
        have hra' : a' % P < P := Ordinal.mod_lt a' hP
        rcases div_mod_lt_of_lt hP ha' with hq | ⟨hq, hr⟩
        · have h1 : ω ^ δ * (a' / P + b / P) + (a' % P ♯ b % P)
              < P * (a' / P + b / P + 1) := by
            rw [mul_add_one]
            exact add_lt_add_right (IH _ _ hra' hrb) _
          have h2 : P * (a' / P + b / P + 1) ≤ P * (a / P + b / P) := by
            refine mul_le_mul_right ?_ P
            rw [Order.add_one_le_iff]
            have hqa' : a' / P < ω := (Ordinal.div_lt hP).2 ha'ω
            obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
            obtain ⟨na', hna'⟩ := Ordinal.lt_omega0.1 hqa'
            obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
            have hlt : na' < na := by
              have h' : (na' : Ordinal) < (na : Ordinal) := by rw [← hna', ← hna]; exact hq
              exact_mod_cast h'
            rw [hna, hna', hnb, ← Nat.cast_add, ← Nat.cast_add, Nat.cast_lt]
            exact Nat.add_lt_add_right hlt nb
          calc a' ♯ b ≤ ω ^ δ * (a' / P + b / P) + (a' % P ♯ b % P) := hstep
            _ < P * (a' / P + b / P + 1) := h1
            _ ≤ P * (a / P + b / P) := h2
            _ ≤ P * (a / P + b / P) + (a % P ♯ b % P) := le_self_add
        · calc a' ♯ b ≤ ω ^ δ * (a' / P + b / P) + (a' % P ♯ b % P) := hstep
            _ = P * (a / P + b / P) + (a' % P ♯ b % P) := by rw [hq]
            _ < P * (a / P + b / P) + (a % P ♯ b % P) :=
                add_lt_add_right (nadd_lt_nadd_right hr _) _
      · intro b' hb'
        have hb'ω : b' < P * ω := hb'.trans hb
        have hstep := IHb b' hb' ha hb'ω
        have hrb' : b' % P < P := Ordinal.mod_lt b' hP
        rcases div_mod_lt_of_lt hP hb' with hq | ⟨hq, hr⟩
        · have h1 : ω ^ δ * (a / P + b' / P) + (a % P ♯ b' % P)
              < P * (a / P + b' / P + 1) := by
            rw [mul_add_one]
            exact add_lt_add_right (IH _ _ hra hrb') _
          have h2 : P * (a / P + b' / P + 1) ≤ P * (a / P + b / P) := by
            refine mul_le_mul_right ?_ P
            rw [Order.add_one_le_iff]
            have hqb' : b' / P < ω := (Ordinal.div_lt hP).2 hb'ω
            obtain ⟨na, hna⟩ := Ordinal.lt_omega0.1 hqa
            obtain ⟨nb, hnb⟩ := Ordinal.lt_omega0.1 hqb
            obtain ⟨nb', hnb'⟩ := Ordinal.lt_omega0.1 hqb'
            have hlt : nb' < nb := by
              have h' : (nb' : Ordinal) < (nb : Ordinal) := by rw [← hnb', ← hnb]; exact hq
              exact_mod_cast h'
            rw [hna, hnb, hnb', ← Nat.cast_add, ← Nat.cast_add, Nat.cast_lt]
            exact Nat.add_lt_add_left hlt na
          calc a ♯ b' ≤ ω ^ δ * (a / P + b' / P) + (a % P ♯ b' % P) := hstep
            _ < P * (a / P + b' / P + 1) := h1
            _ ≤ P * (a / P + b / P) := h2
            _ ≤ P * (a / P + b / P) + (a % P ♯ b % P) := le_self_add
        · calc a ♯ b' ≤ ω ^ δ * (a / P + b' / P) + (a % P ♯ b' % P) := hstep
            _ = P * (a / P + b / P) + (a % P ♯ b' % P) := by rw [hq]
            _ < P * (a / P + b / P) + (a % P ♯ b % P) :=
                add_lt_add_right (nadd_lt_nadd_left hr _) _

/-- The successor step of additive principality. -/
