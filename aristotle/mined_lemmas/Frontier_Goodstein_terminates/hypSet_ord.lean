/-
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Goodstein Terminates
Category: Frontier — Set Theory
Target: Frontier.Goodstein_terminates
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Ordinal

/-! ## Elementary facts about base-`b` digits -/


theorem hypSet_ord (b : ℕ) :
    HypSet Ordinal b (fun a => (Ordinal.omega0) ^ a) (fun a k => a * (k : Ordinal)) where
  zero_le a := bot_le

  add_lt_left a x y h := add_lt_add_right h a
  add_le_left a x y h := (add_le_add_iff_left a).mpr h
  add_zero' a := add_zero a
  mul_one' a := by simp
  mul_mono a k l h := mul_le_mul_right (Nat.cast_le.2 h) a
  mul_succ' a k := by push_cast; rw [mul_add_one]
  pw_pos a := Ordinal.opow_pos a Ordinal.omega0_pos
  pw_mono a c h := Ordinal.opow_le_opow_right Ordinal.omega0_pos h
  pw_step a k _ := by
    show (Ordinal.omega0 ^ a) * ((k + 1 : ℕ) : Ordinal) ≤ Ordinal.omega0 ^ (a + 1)
    rw [opow_add, opow_one]
    exact mul_le_mul_right (le_of_lt (Ordinal.nat_lt_omega0 _)) _
  add_one_le a c h := Order.add_one_le_of_lt h

