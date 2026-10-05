/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- `41` is prime: it is at least `2` and its only divisors are `1` and `41`.
(Stated with the definition of primality unfolded, since the required header comment
must be the first item in the file and therefore no `import` is possible here.) -/

theorem prime_41 : 2 ≤ 41 ∧ ∀ m : Nat, m ∣ 41 → m = 1 ∨ m = 41 := by
  refine ⟨by decide, fun m hm => ?_⟩
  have hle : m ≤ 41 := Nat.le_of_dvd (by decide) hm
  have hall : ∀ k : Nat, k < 42 → k ∣ 41 → k = 1 ∨ k = 41 := by decide
  exact hall m (Nat.lt_succ_of_le hle) hm

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/
