import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The argument is the classical Galois-theoretic one: the quintic `X ^ 5 - 4 * X + 2` is
irreducible over `ℚ` (Eisenstein at `2`), has exactly `3` real roots and hence exactly
`2` non-real complex roots, so its Galois group is the full symmetric group on its `5`
complex roots, which is not solvable.  Consequently none of its roots is expressible by
radicals, i.e. the general quintic equation admits no solution formula in radicals.
-/

open Function Polynomial Polynomial.Gal Ideal

namespace AbelRuffiniDeg5

attribute [local instance] splits_ℚ_ℂ

/-- The quintic `X ^ 5 - 4 * X + 2`, over an arbitrary commutative ring. -/

theorem degree_Q [Nontrivial R] : (Q R).degree = ((5 : ℕ) : WithBot ℕ) := by
  unfold Q
  compute_degree!

variable (R) in
