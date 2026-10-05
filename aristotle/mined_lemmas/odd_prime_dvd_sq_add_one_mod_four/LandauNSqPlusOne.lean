import Mathlib

/-- Landau's fourth problem (**OPEN**), recorded as an unproven `def`:
infinitely many `n` have `n ^ 2 + 1` prime. -/

def LandauNSqPlusOne : Prop := {n : ℕ | (n ^ 2 + 1).Prime}.Infinite

/-- Every odd prime divisor `p` of `n ^ 2 + 1` satisfies `p % 4 = 1`:
in `ZMod p` the element `n` squares to `-1`, so `-1` is a quadratic residue,
which forces `p % 4 ≠ 3`; oddness then leaves only `p % 4 = 1`. -/
