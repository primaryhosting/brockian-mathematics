import Mathlib


def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Landau's `n² + 1` statement is equivalent to the unbounded-witness form:
for every bound `N` there is some `n > N` with `n² + 1` prime. -/
