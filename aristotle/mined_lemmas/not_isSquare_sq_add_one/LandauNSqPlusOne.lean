import Mathlib


def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- For `n > 0`, `n ^ 2 + 1` lies strictly between the consecutive squares
`n ^ 2` and `(n + 1) ^ 2`, hence is never a perfect square. -/
