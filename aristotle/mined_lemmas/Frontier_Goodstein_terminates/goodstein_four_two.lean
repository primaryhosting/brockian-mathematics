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


theorem goodstein_four_two : goodstein 4 2 = 41 := by
  show bump 3 (goodstein 4 1) - 1 = 41
  rw [goodstein_four_one]
  have l26 : Nat.log 3 26 = 2 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have l8 : Nat.log 3 8 = 1 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have l2 : Nat.log 3 2 = 0 := Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  have b2 : bump 3 2 = 2 := by
    rw [bump_eq 3 (by norm_num), l2]; norm_num
  have b8 : bump 3 8 = 10 := by
    rw [bump_eq 3 (by norm_num), l8, bump_one 3]; norm_num [b2]
  rw [bump_eq 3 (by norm_num), l26, b2]
  norm_num [b8]

/-- **Goodstein's theorem**: every Goodstein sequence eventually reaches `0`. -/
