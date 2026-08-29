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

lemma evalFrom_rep {q : σ} {b : List α} (hb : M.evalFrom q b = q) (n : ℕ) :
    M.evalFrom q (rep b n) = q := by
  induction n with
  | zero => simp [DFA.evalFrom]
  | succ n ih => rw [rep_succ, M.evalFrom_of_append, hb, ih]

/--
Pumping lemma for a DFA: every accepted word of length at least `Fintype.card σ`
splits as `a ++ b ++ c` with `|a| + |b| ≤ Fintype.card σ`, `b ≠ []`, and all pumped
words `a ++ bⁿ ++ c` accepted.
-/
