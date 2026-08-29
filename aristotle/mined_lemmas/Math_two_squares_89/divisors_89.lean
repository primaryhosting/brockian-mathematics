/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, spelled out: `n` is at least `2` and its only
divisors are `1` and `n`.  (This is definitionally the same notion as
`Nat.Prime`; it is stated here directly because the required file header must be
the very first thing in the file, which precludes an `import` command.) -/

theorem divisors_89 : ∀ m : Nat, m ∣ 89 → m = 1 ∨ m = 89 := by
  have key : ∀ m < 90, m ∣ 89 → m = 1 ∨ m = 89 := by decide
  intro m hm
  exact key m (Nat.lt_succ_of_le (Nat.le_of_dvd (by decide) hm)) hm

/-- The prime `89` is a sum of two squares: `89 = 5 ^ 2 + 8 ^ 2`. -/
