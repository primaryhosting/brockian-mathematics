/-!
# Two Squares 29
Category: Pure Mathematics
Target: Math.two_squares_29
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, spelled out: `n` is at least `2` and its only
divisors are `1` and `n`. It is stated directly here because the required header
comment must be the very first thing in the file, which rules out any `import`
line, so `Nat.Prime` is not available. -/

theorem divisors_of_29_le : ∀ m : Nat, m ≤ 29 → m ∣ 29 → m = 1 ∨ m = 29 := by decide

/-- `29` is prime. -/
