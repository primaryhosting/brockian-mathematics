import Mathlib


def Superperfect (n : ℕ) : Prop := 0 < n ∧ sigma1 (sigma1 n) = 2 * n

/-- `σ(2^k) = 2^(k+1) - 1`. -/
