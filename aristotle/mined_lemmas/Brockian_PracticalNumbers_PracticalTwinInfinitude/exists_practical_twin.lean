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
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

open Finset Pointwise

/-! ## Basic definitions -/

/-- The sum of the (positive) divisors of `n`. -/

theorem exists_practical_twin (b : ℕ) (hb : 1 ≤ b) :
    ∃ n, 4 * 7 ^ b ≤ n + 2 ∧ Covers n ∧ Covers (n + 2) := by
  obtain ⟨a, ha, h1, h2⟩ := exists_matched_exponents hb
  have hApos : 0 < 3 ^ a := pow_pos (by norm_num) a
  have hBpos : 0 < 7 ^ b := pow_pos (by norm_num) b
  have hcop : Nat.Coprime (3 ^ a) (2 * 7 ^ b) := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact Nat.Coprime.pow_left _ (by norm_num)
    · exact Nat.Coprime.pow _ _ (by norm_num)
  obtain ⟨m, hm1, hm2, hmdvd⟩ := exists_inv_mod (3 ^ a) (2 * 7 ^ b) (by omega) hcop
  obtain ⟨m', hm'⟩ := hmdvd
  have hm'pos : 0 < m' := by
    rcases Nat.eq_zero_or_pos m' with h | h
    · rw [h, mul_zero] at hm'; omega
    · exact h
  have heq : 2 * 3 ^ a * m + 2 = 4 * 7 ^ b * m' := by
    calc 2 * 3 ^ a * m + 2 = 2 * (3 ^ a * m + 1) := by ring
      _ = 2 * (2 * 7 ^ b * m') := by rw [hm']
      _ = 4 * 7 ^ b * m' := by ring
  have hm'le : m' ≤ 3 ^ a := by
    by_contra hcon
    push_neg at hcon
    have hstep : 2 * 7 ^ b * (3 ^ a + 1) ≤ 2 * 7 ^ b * m' :=
      Nat.mul_le_mul_left _ (by omega)
    have hexp : 2 * 7 ^ b * (3 ^ a + 1) = 2 * (7 ^ b * 3 ^ a) + 2 * 7 ^ b := by ring
    have hsmall : 3 ^ a * m ≤ 2 * (7 ^ b * 3 ^ a) := by
      calc 3 ^ a * m ≤ 3 ^ a * (2 * 7 ^ b) := Nat.mul_le_mul_left _ hm2
        _ = 2 * (7 ^ b * 3 ^ a) := by ring
    have h7 : 2 ≤ 2 * 7 ^ b := by omega
    omega
  have hodd : ¬ 2 ∣ m := by
    intro hd
    have h2dvd : (2 : ℕ) ∣ 3 ^ a * m + 1 := ⟨7 ^ b * m', by rw [hm']; ring⟩
    have hAm : (2 : ℕ) ∣ 3 ^ a * m := Dvd.dvd.mul_left hd (3 ^ a)
    have hsub : (2 : ℕ) ∣ 1 := (Nat.dvd_add_right hAm).mp h2dvd
    omega
  refine ⟨2 * 3 ^ a * m, ?_, ?_, ?_⟩
  · have : 4 * 7 ^ b * 1 ≤ 4 * 7 ^ b * m' := Nat.mul_le_mul_left _ hm'pos
    omega
  · exact covers_two_mul_three_pow_mul ha (by omega) hodd (by omega)
  · rw [heq]
    exact covers_four_mul_seven_pow_mul hb hm'pos (by omega)

/-! ## Main theorem -/

/-- **Practical twin infinitude**: there are infinitely many `n` such that both `n` and
`n + 2` are practical numbers. -/
