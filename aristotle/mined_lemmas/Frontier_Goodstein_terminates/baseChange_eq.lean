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


lemma baseChange_eq (b c : ℕ) {n : ℕ} (hn : n ≠ 0) :
    baseChange b c n = c ^ (baseChange b c (Nat.log b n)) * (n / b ^ Nat.log b n) +
      baseChange b c (n % b ^ Nat.log b n) := by
  rw [baseChange]; simp [hn]

/-! ### Monotonicity of the ordinal evaluation -/

