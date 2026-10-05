/-!
# Ramsey 3 3
Category: Pure Mathematics
Target: Math.ramsey_3_3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- An auxiliary "vector" of five booleans, read off as a function on `Fin 6` (the value at
the index `0` is irrelevant and set to `false`). -/

private theorem exists_three_equal (b1 b2 b3 b4 b5 : Bool) :
    ∃ x y z : Fin 6, 0 < x ∧ x < y ∧ y < z ∧
      boolVec b1 b2 b3 b4 b5 x = boolVec b1 b2 b3 b4 b5 y ∧
      boolVec b1 b2 b3 b4 b5 y = boolVec b1 b2 b3 b4 b5 z := by
  revert b1 b2 b3 b4 b5; decide

