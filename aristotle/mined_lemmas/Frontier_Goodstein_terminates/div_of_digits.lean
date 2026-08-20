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


lemma div_of_digits {c E d r : ℕ} (hr : r < c ^ E) : (c ^ E * d + r) / c ^ E = d := by
  have h : 0 < c ^ E := by omega
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ h, Nat.div_eq_of_lt hr, Nat.zero_add]

