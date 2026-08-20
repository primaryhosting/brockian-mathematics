/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `n` is a sum of two squares. -/

def IsSumOfTwoSquares (n : Nat) : Prop := ∃ a b : Nat, n = a ^ 2 + b ^ 2

/-- `n` is prime: it is at least `2` and its only divisor below `n` is `1`. -/
