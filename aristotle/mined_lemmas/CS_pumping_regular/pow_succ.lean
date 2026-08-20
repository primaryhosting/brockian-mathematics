/-
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Pumping Regular
Category: Computer Science
Target: CS.pumping_regular
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

variable {α : Type*}

/-- The `n`-fold concatenation of the word `b` with itself. -/

@[simp] lemma pow_succ (b : List α) (n : ℕ) : pow b (n + 1) = b ++ pow b n := by
  simp [pow, List.replicate_succ]

