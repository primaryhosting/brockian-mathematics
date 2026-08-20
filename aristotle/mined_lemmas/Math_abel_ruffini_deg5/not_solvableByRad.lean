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

theorem not_solvableByRad (x : ℂ) (hx : aeval x (Q ℚ) = 0) : ¬ IsSolvableByRad ℚ x :=
  fun h => not_solvable_gal_Q (solvableByRad.isSolvable' irreducible_Q hx h)

end AbelRuffiniDeg5

namespace Math

open AbelRuffiniDeg5 in
/-- **Abel–Ruffini theorem in degree 5.** The general quintic equation is not solvable by
radicals: there is a quintic polynomial over `ℚ` (namely `X ^ 5 - 4 * X + 2`) which is
irreducible, whose Galois group is not solvable, and none of whose (existing) complex roots
is expressible by radicals over `ℚ`. -/
