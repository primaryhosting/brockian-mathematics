import Mathlib

/-!
# Zeckendorf Small
Category: Fibonacci
Target: Fibonacci.zeckendorf_small
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Fibonacci

/-- Key intermediate lemma: the values of the three Fibonacci numbers involved. -/
lemma fib_values : Nat.fib 11 = 89 ∧ Nat.fib 6 = 8 ∧ Nat.fib 4 = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Nat.fib]

/-- Zeckendorf representation of 100: `100 = fib 11 + fib 6 + fib 4`,
a sum of Fibonacci numbers with indices `11, 6, 4` pairwise differing by at least 2. -/
theorem zeckendorf_small : 100 = Nat.fib 11 + Nat.fib 6 + Nat.fib 4 := by
  obtain ⟨h11, h6, h4⟩ := fib_values
  rw [h11, h6, h4]

end Fibonacci

