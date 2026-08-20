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


theorem hbEval_lt_opow {b : ℕ} (hb : 2 ≤ b) {n k : ℕ} (h : n < b ^ k) :
    hbEval b n < Ordinal.omega0 ^ hbEval b k :=
  (hbEval_key hb k).2 k le_rfl n h

/-! ### Monotonicity of the base change -/

