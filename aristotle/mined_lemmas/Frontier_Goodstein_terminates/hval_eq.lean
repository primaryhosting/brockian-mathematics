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


theorem hval_eq {α : Type*} [Zero α] [Add α] (b : ℕ) (pw : α → α) (mul : α → ℕ → α)
    {n : ℕ} (hn : n ≠ 0) :
    hval b pw mul n =
      mul (pw (hval b pw mul (Nat.log b n))) (n / b ^ Nat.log b n)
        + hval b pw mul (n % b ^ Nat.log b n) := by
  rw [hval]; simp [hn]

/-- The properties of `pw`, `mul` and the order on `α` needed for the argument. -/
structure HypSet (α : Type*) [LinearOrder α] [Zero α] [One α] [Add α]
    (b : ℕ) (pw : α → α) (mul : α → ℕ → α) : Prop where
  zero_le : ∀ a : α, 0 ≤ a
  add_lt_left : ∀ a x y : α, x < y → a + x < a + y
  add_le_left : ∀ a x y : α, x ≤ y → a + x ≤ a + y
  add_zero' : ∀ a : α, a + 0 = a
  mul_one' : ∀ a : α, mul a 1 = a
  mul_mono : ∀ (a : α) (k l : ℕ), k ≤ l → mul a k ≤ mul a l
  mul_succ' : ∀ (a : α) (k : ℕ), mul a (k + 1) = mul a k + a
  pw_pos : ∀ a : α, 0 < pw a
  pw_mono : ∀ a c : α, a ≤ c → pw a ≤ pw c
  pw_step : ∀ (a : α) (k : ℕ), k ≤ b → mul (pw a) (k + 1) ≤ pw (a + 1)
  add_one_le : ∀ a c : α, a < c → a + 1 ≤ c

section Generic

variable {α : Type*} [LinearOrder α] [Zero α] [One α] [Add α]
  {b : ℕ} {pw : α → α} {mul : α → ℕ → α}

