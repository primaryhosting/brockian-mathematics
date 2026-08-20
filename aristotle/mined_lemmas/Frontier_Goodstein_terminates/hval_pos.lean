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


theorem hval_pos (h : HypSet α b pw mul) {n : ℕ} (hn : n ≠ 0) : 0 < hval b pw mul n := by
  rw [hval_eq b pw mul hn]
  set A := pw (hval b pw mul (Nat.log b n)) with hA
  calc (0 : α) < A := h.pw_pos _
    _ = mul A 1 := (h.mul_one' _).symm
    _ ≤ mul A (n / b ^ Nat.log b n) := h.mul_mono _ _ _ (digit_pos hn)
    _ ≤ mul A (n / b ^ Nat.log b n) + hval b pw mul (n % b ^ Nat.log b n) := by
        have := h.add_le_left (mul A (n / b ^ Nat.log b n)) 0
          (hval b pw mul (n % b ^ Nat.log b n)) (h.zero_le _)
        simpa [h.add_zero'] using this

/-- The two key facts, proved by simultaneous strong induction:
`hval` is strictly monotone, and it maps `[0, b^E)` below `pw (hval E)`. -/
