/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header above
-- is written as a plain comment and repeated as a module docstring after the import.)

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A sequence `f : ℕ → ℤ` is a `±1` sequence if `f n ∈ {1, -1}` for every `n ≥ 1`
(the value `f 0` is irrelevant, since homogeneous arithmetic progressions only use
indices `i * d` with `i, d ≥ 1`). -/

theorem isPMOne_seq11 : IsPMOne seq11 := by
  intro n hn
  rcases lt_or_ge n 12 with h | h
  · interval_cases n <;> decide
  · exact Or.inl (List.getD_eq_default _ _ (by simpa using h))

/-- **Sharpness of the bound `12`.**  All homogeneous arithmetic progressions contained in
`{1, …, 11}` have discrepancy at most `1` for the sequence `seq11`, so the conclusion of
`Frontier.erdos_discrepancy` fails if `12` is replaced by `11`. -/
