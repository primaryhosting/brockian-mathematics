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


lemma omega_mul_le {a : Ordinal.{0}} {x y : Ordinal.{0}} (h : x ≤ y) :
    omega0 ^ a * x ≤ omega0 ^ a * y := mul_le_mul_right h _

