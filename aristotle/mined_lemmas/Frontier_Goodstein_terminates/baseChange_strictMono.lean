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


theorem baseChange_strictMono {b c : ℕ} (hb : 2 ≤ b) (hbc : b ≤ c) :
    StrictMono (baseChange b c) := by
  intro m n h
  exact (baseChange_key hb hbc n).1 n le_rfl m h

