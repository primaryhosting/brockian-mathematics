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

lemma rep_succ {α : Type*} (b : List α) (n : ℕ) : rep b (n + 1) = b ++ rep b n := by
  simp [rep, List.replicate_succ]

/-! ### Pumping for a fixed DFA

The pigeonhole step: among the `|σ| + 1` states reached after reading the prefixes of `x`
of lengths `0, 1, …, |σ|`, two must coincide, and the corresponding infix of `x` is a loop.
-/

variable {α σ : Type*} [Fintype σ] (M : DFA α σ)

omit [Fintype σ] in
/-- Reading a loop word `b` (i.e. `M.evalFrom q b = q`) any number of times stays at `q`. -/
