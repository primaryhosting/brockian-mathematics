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

private def boolVec (b1 b2 b3 b4 b5 : Bool) : Fin 6 → Bool
  | 0 => false
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | 4 => b4
  | 5 => b5

/-- Pigeonhole principle: among the five booleans `b1, …, b5` there are three, at strictly
increasing indices, that are equal. -/
