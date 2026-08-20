/-!
# Kervaire Invariant
Category: Frontier Math
Target: Math2.kervaire_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Math2

/-- The dimensions in which the Kervaire invariant is known (or, in the single remaining
edge case, permitted) to be nonzero: `2, 6, 14, 30, 62, 126`. -/

def IsKervaireDimension (n : Nat) : Prop :=
  n = 2 ∨ n = 6 ∨ n = 14 ∨ n = 30 ∨ n = 62 ∨ n = 126

/-- **Browder's constraint, arithmetic form.**  A positive natural number `n` with `n + 2` a
power of two and `n ≤ 126` is one of `2, 6, 14, 30, 62, 126`. -/
