import Mathlib

/-- `4 / n` is a sum of three unit fractions with positive denominators. -/

def ErdosStrausConjecture : Prop :=
  ∀ n : ℕ, 2 ≤ n → ErdosStrausSolvable n

/-- For `n ≡ 2 (mod 3)`, writing `n = 3k + 2`, the identity
`4/n = 1/n + 1/(k+1) + 1/(n(k+1))` gives an explicit representation. -/
