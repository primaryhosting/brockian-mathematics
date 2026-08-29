import Mathlib
import RequestProject.TwoSquares5

/-!
# Two Squares 5 (Mathlib phrasing)

A restatement of `Math.two_squares_5` using Mathlib's `Nat.Prime`, together with a proof that the
explicit primality condition appearing in `Math.two_squares_5` really is `Nat.Prime 5`.
-/

namespace Math

/-- The prime `5` is a sum of two squares: `5 = 1 ^ 2 + 2 ^ 2`. -/

theorem two_squares_5_mathlib : Nat.Prime 5 ∧ ∃ a b : ℕ, 5 = a ^ 2 + b ^ 2 :=
  ⟨two_squares_5_prime_spec.mp two_squares_5.1, two_squares_5.2⟩

end Math

/-!
# Two Squares 5
Category: Pure Mathematics
Target: Math.two_squares_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/--
**The prime `5` is a sum of two squares.**

The statement asserts both that `5` is prime (spelled out as: `2 ≤ 5` and every divisor of `5`
is `1` or `5`) and that `5 = 1 ^ 2 + 2 ^ 2`.

Primality is written out explicitly rather than via `Nat.Prime` so that this file, which must
begin with the required header comment, needs no `import` line (Lean requires imports to be the
very first commands in a file).  A Mathlib-phrased version using `Nat.Prime` is given in
`RequestProject/TwoSquares5Mathlib.lean`.

The proof of the divisor condition is the contrapositive-style reformulation suggested: instead of
reasoning about primality abstractly, we note that any divisor `m` of `5` satisfies `m ≤ 5` and
`5 % m = 0`, which leaves only finitely many cases to check.
-/
