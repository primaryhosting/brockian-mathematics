import Mathlib


def aliquot (n : ℕ) : ℕ := ∑ d ∈ n.properDivisors, d

