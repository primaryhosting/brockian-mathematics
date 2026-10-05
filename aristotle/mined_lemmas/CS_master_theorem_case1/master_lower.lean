import Mathlib

/-!
# Master Theorem Case 1
Category: Computer Science
Target: CS.master_theorem_case1
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on file layout: Lean 4 requires `import` commands to be the very first commands of a
module, so the header module docstring above is placed immediately after the import.
-/

namespace CS

open Real

section

variable {a b C ε : ℝ} {T f : ℕ → ℝ}

/-- On exact powers of `b`, `(b^k)^(log_b a) = a^k`. -/

lemma master_lower (ha : 0 < a)
    (hrec : ∀ k, T (k + 1) = a * T k + f (k + 1))
    (hfnn : ∀ k, 0 ≤ f k) (k : ℕ) : a ^ k * T 0 ≤ T k := by
  induction k with
  | zero => simp
  | succ n ih =>
      have := hfnn (n + 1)
      rw [hrec n, pow_succ]
      nlinarith [ih, ha]

/-- Upper bound with the geometric-sum invariant. -/
