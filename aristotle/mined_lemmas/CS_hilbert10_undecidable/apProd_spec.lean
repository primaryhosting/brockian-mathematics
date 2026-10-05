import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem apProd_spec (a b m y : ℕ) :
    y = apProd a b m ↔
      (b = 0 ∧ y = a ^ m) ∨
      (1 ≤ b ∧ y < b * (a + m*b)^m + 1 ∧
        ∃ c, (b * c) % (b * (a + m*b)^m + 1) = a % (b * (a + m*b)^m + 1) ∧
          y % (b * (a + m*b)^m + 1)
            = (b^m * (m.factorial * (c + m).choose m)) % (b * (a + m*b)^m + 1)) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · constructor
    · rintro rfl
      exact Or.inl ⟨rfl, by simp [apProd, Nat.card_Icc]⟩
    · rintro (⟨-, rfl⟩ | ⟨h, -⟩)
      · simp [apProd, Nat.card_Icc]
      · omega
  · set K := (a + m*b)^m with hK
    set M := b * K + 1 with hM
    have hMK : K < M := by
      have : K ≤ b * K := Nat.le_mul_of_pos_left _ hb
      omega
    have hprod : apProd a b m < M := lt_of_le_of_lt (apProd_le a b m) hMK
    have hinv : ∃ c, b * c ≡ a [MOD M] := by
      refine ⟨(a * (M - K)) % M, ?_⟩
      have h1 : b * ((a * (M - K)) % M) ≡ b * (a * (M - K)) [MOD M] :=
        Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
      refine h1.trans ?_
      have hcomm : M * b = b * M := Nat.mul_comm _ _
      have hbK : b * K = M - 1 := by omega
      have h5 : M ≤ M * b := Nat.le_mul_of_pos_right _ hb
      have h6 : b * K ≤ b * M := Nat.mul_le_mul_left _ (le_of_lt hMK)
      have hbm : b * (M - K) = M * (b-1) + 1 := by
        have h3 : b * (M - K) = b * M - b * K := by rw [Nat.mul_sub]
        have h4 : M * (b - 1) = M * b - M := by rw [Nat.mul_sub]; simp
        omega
      have h2 : b * (a * (M - K)) = a + (a*(b-1))*M := by
        calc b * (a * (M - K)) = a * (b * (M - K)) := by ring
          _ = a * (M * (b-1) + 1) := by rw [hbm]
          _ = a + (a*(b-1))*M := by ring
      rw [h2]
      have h8 : a + (a*(b-1))*M ≡ a + 0 [MOD M] :=
        Nat.ModEq.add_left a ((Nat.modEq_zero_iff_dvd).2 ⟨a*(b-1), by ring⟩)
      simpa using h8
    obtain ⟨c0, hc0⟩ := hinv
    constructor
    · rintro rfl
      refine Or.inr ⟨hb, hprod, c0 % M, ?_, ?_⟩
      · exact (Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)).trans hc0
      · exact apProd_modEq a b (c0 % M) m M
          ((Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)).trans hc0)
    · rintro (⟨h, -⟩ | ⟨-, hy, c, hc1, hc2⟩)
      · omega
      · have h1 : apProd a b m ≡ b ^ m * (m.factorial * (c + m).choose m) [MOD M] :=
          apProd_modEq a b c m M hc1
        have h7 : y ≡ apProd a b m [MOD M] := Nat.ModEq.trans hc2 (Nat.ModEq.symm h1)
        exact Nat.ModEq.eq_of_lt_of_lt h7 hy hprod

/-- Products of arithmetic progressions are Diophantine. -/
