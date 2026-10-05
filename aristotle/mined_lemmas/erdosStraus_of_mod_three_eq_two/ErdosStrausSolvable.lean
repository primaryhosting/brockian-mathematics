import Mathlib

/-- `4 / n` is a sum of three unit fractions with positive denominators. -/

def ErdosStrausSolvable (n : ℕ) : Prop :=
  ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    (4 : ℚ) / (n : ℚ) = 1 / (a : ℚ) + 1 / (b : ℚ) + 1 / (c : ℚ)

/-- The Erdős–Straus conjecture (**OPEN**), recorded as an unproven
`def`: every `n ≥ 2` admits such a representation. -/
