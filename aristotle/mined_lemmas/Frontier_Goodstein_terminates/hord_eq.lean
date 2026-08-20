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


theorem hord_eq (b : ℕ) {n : ℕ} (hn : n ≠ 0) :
    hord b n = Ordinal.omega0 ^ (hord b (Nat.log b n)) * ((n / b ^ Nat.log b n : ℕ) : Ordinal)
      + hord b (n % b ^ Nat.log b n) := hval_eq _ _ _ hn

