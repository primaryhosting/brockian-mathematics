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


@[simp] theorem hval_zero {α : Type*} [Zero α] [Add α] (b : ℕ) (pw : α → α) (mul : α → ℕ → α) :
    hval b pw mul 0 = 0 := by
  rw [hval]; simp

