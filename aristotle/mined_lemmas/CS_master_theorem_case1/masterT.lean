/-
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-- The divide-and-conquer recurrence `T(n) = a * T(n / b) + f(n)`, sampled along the
exact powers `n = b ^ k` of the branching factor.  `masterT a f T₀ k` is the value of
`T` at `n = b ^ k`, and `f k` stands for the driving cost `f (b ^ k)`. -/

noncomputable def masterT (a : ℝ) (f : ℕ → ℝ) (T₀ : ℝ) : ℕ → ℝ
  | 0 => T₀
  | (k + 1) => a * masterT a f T₀ k + f (k + 1)

section

variable {a b : ℝ}

/-- `(b ^ k) ^ (log_b a) = a ^ k`. -/
