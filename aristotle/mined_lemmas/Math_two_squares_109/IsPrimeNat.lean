/-!
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, stated elementarily: `n` is at least `2` and its only
proper divisor is `1`.  (See `Math.isPrimeNat_iff_prime` in `RequestProject.MathMathlib`
for the proof that this agrees with Mathlib's `Nat.Prime`.) -/

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m, m < n → m ∣ n → m = 1

/-- **Two squares, 109.**  The prime `109` is a sum of two squares: `109 = 10 ^ 2 + 3 ^ 2`. -/
