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


theorem bump_lt_pow {b : ℕ} (hb : 2 ≤ b) {E m : ℕ} (hm : m < b ^ E) :
    bump b m < (b + 1) ^ (bump b E) := hval_lt_pw (hypSet_nat b) hb hm

