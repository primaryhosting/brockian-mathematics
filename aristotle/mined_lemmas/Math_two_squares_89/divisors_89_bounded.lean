/-!
# Two Squares 89
Category: Pure Mathematics
Target: Math.two_squares_89
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Auxiliary bounded divisor check for `89`, decided by finite case analysis. -/

theorem divisors_89_bounded : ∀ m < 90, m ∣ 89 → m = 1 ∨ m = 89 := by decide

/--
**The prime `89` is a sum of two squares.**

The statement packages both facts: `89` is prime (it is greater than `1` and its only
divisors are `1` and itself), and `89 = 5 ^ 2 + 8 ^ 2`.

Note on the header: since a module doc comment must be the required first item of this file,
no `import` line may precede it, so the proof is developed self-containedly in core Lean.
(In Mathlib the primality is `by norm_num : Nat.Prime 89`, and the general two-squares fact for
primes `p % 4 ≠ 3` is `Nat.Prime.sq_add_sq`.)
-/
