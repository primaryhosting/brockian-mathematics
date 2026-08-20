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


lemma omega_mul_add_lt {a x : Ordinal.{0}} {d : ℕ} (hx : x < omega0 ^ a) :
    omega0 ^ a * (d : Ordinal) + x < omega0 ^ a * ((d : Ordinal) + 1) := by
  rw [mul_add, mul_one]
  exact (add_lt_add_iff_left _).2 hx

