import Mathlib

/-!
# Abc Statement
Category: Frontier — Prime Numbers
Target: Frontier.abc_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Frontier

/-- The radical of a natural number: the product of its distinct prime factors. -/

lemma abcExceptions_anti {δ ε : ℝ} (h : δ ≤ ε) : AbcExceptions ε ⊆ AbcExceptions δ := by
  rintro ⟨a, b, c⟩ ⟨ha, hb, habc, hcop, hlt⟩
  refine ⟨ha, hb, habc, hcop, lt_of_le_of_lt ?_ hlt⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast one_le_rad) (by linarith)

/-- **The abc conjecture, formalized**, together with two Lean-checked facts about it:

* it suffices to prove it for all small `ε` (reduction), and
* the statement genuinely fails for `ε = 0`: there are infinitely many coprime triples
  `a + b = c` with `rad (a * b * c) < c`. -/
