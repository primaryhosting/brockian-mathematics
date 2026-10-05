import Mathlib

/-- Landau's problem: there are infinitely many `n` with `n ^ 2 + 1` prime. -/

def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Landau's `n ^ 2 + 1` problem is equivalent to its even sub-sequence version:
for odd `n > 1` the number `n ^ 2 + 1` is even and larger than `2`, hence composite,
so the only odd witness is `n = 1`. -/
