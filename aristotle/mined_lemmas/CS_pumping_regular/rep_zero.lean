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

@[simp] lemma rep_zero {α : Type*} (b : List α) : rep b 0 = [] := rfl

