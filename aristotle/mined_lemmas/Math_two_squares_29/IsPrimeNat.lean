/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `n` is a sum of two squares. -/

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ m : Nat, m < n → m ∣ n → m = 1

/-- Key intermediate lemma: `29 = 2 ^ 2 + 5 ^ 2`. -/
