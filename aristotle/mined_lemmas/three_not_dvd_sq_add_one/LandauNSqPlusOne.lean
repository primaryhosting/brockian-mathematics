import Mathlib


def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Squares are `0` or `1` mod `3`, hence `n ^ 2 + 1` is never divisible by `3`. -/
