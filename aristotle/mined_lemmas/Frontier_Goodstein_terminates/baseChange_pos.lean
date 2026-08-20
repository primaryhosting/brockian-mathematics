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

/-! ### Elementary facts about base-`b` digits -/


lemma baseChange_pos {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) {n : ℕ} (hn : n ≠ 0) :
    0 < baseChange b c n := by
  have := baseChange_strictMono hb hbc (Nat.pos_of_ne_zero hn)
  simpa using this

/-! ### The base change does not change the ordinal value -/

