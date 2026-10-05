import Mathlib


def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- For even `n > 1`, the odd number `n ^ 2 + 1` exceeds `1`, so it has an odd prime factor,
and every odd prime factor of `n ^ 2 + 1` is congruent to `1` mod `4` (since `-1` is a square
mod such a prime). -/
