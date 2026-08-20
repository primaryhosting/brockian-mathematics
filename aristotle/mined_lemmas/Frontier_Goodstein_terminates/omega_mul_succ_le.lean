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


lemma omega_mul_succ_le {a : Ordinal.{0}} {d : ℕ} :
    omega0 ^ a * ((d : Ordinal) + 1) ≤ omega0 ^ (a + 1) := by
  rw [opow_add, opow_one]
  refine mul_le_mul_right ?_ _
  have h : ((d + 1 : ℕ) : Ordinal) < omega0 := nat_lt_omega0 _
  push_cast at h
  exact h.le

