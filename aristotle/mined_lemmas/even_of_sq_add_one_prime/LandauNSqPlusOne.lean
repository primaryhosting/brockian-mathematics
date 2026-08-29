import Mathlib

/-- Landau's fourth problem (**OPEN**), recorded as an unproven `def`:
infinitely many `n` have `n ^ 2 + 1` prime. -/

def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

