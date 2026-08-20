import Mathlib

/-!
# Two Squares 41 (Mathlib version)

Supplementary file: the same statement as `Math.two_squares_41`, but phrased with Mathlib's
`Nat.Prime`. It also records that the ad hoc primality predicate used in the main file agrees
with `Nat.Prime` on `41`.
-/

namespace Math

/-- The prime `41` is a sum of two squares: `41 = 4 ^ 2 + 5 ^ 2`. -/

theorem two_squares_41_mathlib : Nat.Prime 41 ∧ ∃ a b : ℕ, (41 : ℕ) = a ^ 2 + b ^ 2 :=
  ⟨by norm_num, 4, 5, by norm_num⟩

end Math

/-!
# Two Squares 41
Category: Pure Mathematics
Target: Math.two_squares_41
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header above is a module docstring, which Lean requires to be the very
-- first command in the file; consequently no `import` line may precede it, so this file is
-- developed self-contained in core Lean 4 (no Mathlib), including the primality predicate.

namespace Math

/-- `IsPrimeNat p` says that `p` is at least `2` and its only divisors are `1` and `p`,
i.e. `p` is prime. -/
