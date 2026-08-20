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


theorem hbEval_strictMono {b : ℕ} (hb : 2 ≤ b) : StrictMono (hbEval b) := by
  intro m n h
  exact (hbEval_key hb n).1 n le_rfl m h

