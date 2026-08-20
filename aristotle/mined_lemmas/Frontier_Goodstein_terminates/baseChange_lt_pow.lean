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


theorem baseChange_lt_pow {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) {n k : ℕ} (h : n < b ^ k) :
    baseChange b c n < c ^ baseChange b c k :=
  (baseChange_key hb hbc k).2 k le_rfl n h

