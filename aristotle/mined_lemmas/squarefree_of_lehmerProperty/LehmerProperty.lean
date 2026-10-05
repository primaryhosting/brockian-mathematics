import Mathlib

/-- `n` has the Lehmer property: `φ n` divides `n - 1`. -/

def LehmerProperty (n : ℕ) : Prop := Nat.totient n ∣ n - 1

/-- Lehmer's totient problem (**OPEN**), recorded as an unproven `def`:
only primes have the Lehmer property (above 1). -/
