/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

open Language Computability

/-- `pump y i` is the concatenation of `i` copies of the word `y`. -/

def pump {α : Type*} (y : List α) (i : ℕ) : List α :=
  (List.replicate i y).flatten

