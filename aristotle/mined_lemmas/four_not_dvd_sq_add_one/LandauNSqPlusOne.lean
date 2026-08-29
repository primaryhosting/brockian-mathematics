import Mathlib


def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- `n ^ 2 + 1` is never divisible by `4`: squares are `0` or `1` mod `4`, so
`n ^ 2 + 1` is `1` or `2` mod `4`. -/
