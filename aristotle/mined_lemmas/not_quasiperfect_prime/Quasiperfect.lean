import Mathlib


def Quasiperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 n = 2 * n + 1

/-- No prime is quasiperfect: for a prime `p`, `sigma1 p = 1 + p < 2 * p + 1`. -/
