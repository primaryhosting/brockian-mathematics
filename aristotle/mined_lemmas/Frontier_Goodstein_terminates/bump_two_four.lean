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


theorem bump_two_four : bump 2 4 = 27 := by
  have l4 : Nat.log 2 4 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have l2 : Nat.log 2 2 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have b2 : bump 2 2 = 3 := by
    rw [bump_eq 2 (by norm_num), l2, bump_one 2]
    norm_num
  rw [bump_eq 2 (by norm_num), l4, b2]
  norm_num

