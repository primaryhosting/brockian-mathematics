/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace CS

/-! ### The `n`-fold power of a word -/

/-- `rep b n` is the `n`-fold concatenation `bⁿ` of the word `b` with itself. -/

def rep {α : Type*} (b : List α) (n : ℕ) : List α :=
  (List.replicate n b).flatten

