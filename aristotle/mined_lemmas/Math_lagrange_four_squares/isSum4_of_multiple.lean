/-
# Lagrange Four Squares
Category: Pure Mathematics
Target: Math.lagrange_four_squares
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede any module docstring (`/-! ... -/`),
-- so the header above is written as an ordinary block comment.

import Mathlib

/-!
This file contains a self-contained proof of Lagrange's four-square theorem, following
Lagrange's classical descent argument:

* `Math.euler_identity` : Euler's four-square identity;
* `Math.IsSum4.mul` : the sums of four squares are closed under multiplication;
* `Math.exists_mul_isSum4_of_prime` : some multiple `m * p` with `0 < m < p` of a prime `p`
  is a sum of four squares;
* `Math.isSum4_of_two_mul` and `Math.descent_odd` : the two descent steps;
* `Math.prime_isSum4` : every prime is a sum of four squares;
* `Math.lagrange_four_squares` : every natural number is a sum of four squares.
-/

namespace Math

/-- `IsSum4 n` states that the integer `n` is a sum of four integer squares. -/

private theorem isSum4_of_multiple {p : ℕ} (hp : p.Prime) :
    ∀ m : ℕ, 0 < m → m < p → IsSum4 ((m : ℤ) * p) → IsSum4 (p : ℤ) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 hmp h
    by_cases hm1 : m = 1
    · subst hm1; simpa using h
    · by_cases hpar : m % 2 = 0
      · obtain ⟨m', rfl⟩ : ∃ m', m = 2 * m' := ⟨m / 2, by omega⟩
        have h2 : IsSum4 (2 * ((m' : ℤ) * p)) := by
          have e : ((2 * m' : ℕ) : ℤ) * p = 2 * ((m' : ℤ) * p) := by push_cast; ring
          rwa [e] at h
        exact ih m' (by omega) (by omega) (by omega) (isSum4_of_two_mul h2)
      · obtain ⟨r, hr0, hrm, hr⟩ := descent_odd hp (by omega) hmp (by omega) h
        exact ih r hrm hr0 (by omega) hr

/-- Every prime is a sum of four squares. -/
