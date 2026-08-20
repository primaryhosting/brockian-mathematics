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


lemma hbEval_eq (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hbEval b n = Ordinal.omega0 ^ (hbEval b (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ) : Ordinal) +
      hbEval b (n % b ^ Nat.log b n) := by
  rw [hbEval]; simp [hn]

