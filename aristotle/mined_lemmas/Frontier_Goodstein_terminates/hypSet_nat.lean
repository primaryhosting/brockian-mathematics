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


theorem hypSet_nat (b : ℕ) : HypSet ℕ b (fun a => (b + 1) ^ a) (fun a k => a * k) where
  zero_le a := Nat.zero_le a
  add_lt_left a x y h := by omega
  add_le_left a x y h := by omega
  add_zero' a := by omega
  mul_one' a := by simp
  mul_mono a k l h := Nat.mul_le_mul_left a h
  mul_succ' a k := by ring
  pw_pos a := pow_pos (Nat.succ_pos b) a
  pw_mono a c h := Nat.pow_le_pow_right (Nat.succ_pos b) h
  pw_step a k hk := by
    show ((b + 1) ^ a) * (k + 1) ≤ (b + 1) ^ (a + 1)
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ (by omega)
  add_one_le a c h := h

