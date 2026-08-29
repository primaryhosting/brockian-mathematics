import Mathlib

/-!
# Reals Uncountable
Category: Frontier — Set Theory
Target: Infinity.reals_uncountable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module doc comments, so the header block above sits immediately after `import Mathlib`.

namespace Infinity

/-- `ℝ` is not a countable type. -/

theorem not_countable_real : ¬ Countable ℝ := fun h =>
  Cardinal.not_countable_real (Set.countable_univ_iff.mpr h)

/-- The real numbers are uncountable: there is no surjection from `ℕ` onto `ℝ`. -/
