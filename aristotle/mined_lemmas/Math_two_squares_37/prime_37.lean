/-!
# Two Squares 37
Category: Pure Mathematics
Target: Math.two_squares_37
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `37` is prime: its only divisors are `1` and `37` (and it is greater than `1`). -/

theorem prime_37 : 1 < 37 ∧ ∀ m : Nat, m ∣ 37 → m = 1 ∨ m = 37 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have h1 : m ≤ 37 := Nat.le_of_dvd (by decide) hm
  have h2 : ∀ k : Nat, k < 38 → k ∣ 37 → k = 1 ∨ k = 37 := by decide
  exact h2 m (by omega) hm

/-- The prime `37` is a sum of two squares: `37 = 1 ^ 2 + 6 ^ 2`. -/
