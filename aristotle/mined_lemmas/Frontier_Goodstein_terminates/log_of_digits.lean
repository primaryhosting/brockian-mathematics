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


lemma log_of_digits {c E d r : ℕ} (hd0 : 0 < d) (hdc : d < c) (hr : r < c ^ E) :
    Nat.log c (c ^ E * d + r) = E := by
  refine Nat.log_eq_of_pow_le_of_lt_pow ?_ ?_
  · calc c ^ E = c ^ E * 1 := by ring
      _ ≤ c ^ E * d := Nat.mul_le_mul_left _ hd0
      _ ≤ _ := Nat.le_add_right _ _
  · calc c ^ E * d + r < c ^ E * d + c ^ E := by omega
      _ = c ^ E * (d + 1) := by ring
      _ ≤ c ^ E * c := Nat.mul_le_mul_left _ (by omega)
      _ = c ^ (E + 1) := by ring

