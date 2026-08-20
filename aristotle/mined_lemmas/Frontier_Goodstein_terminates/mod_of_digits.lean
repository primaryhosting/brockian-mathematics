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


lemma mod_of_digits {c E d r : ℕ} (hr : r < c ^ E) : (c ^ E * d + r) % c ^ E = r := by
  rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-! ### Hereditary base-`b` representations -/

/-- `hbEval b n` is the ordinal obtained by writing `n` in hereditary base `b`
(i.e. writing `n` in base `b`, and recursively writing the exponents in base `b` as well)
and then replacing every occurrence of the base `b` by the ordinal `ω`. -/
