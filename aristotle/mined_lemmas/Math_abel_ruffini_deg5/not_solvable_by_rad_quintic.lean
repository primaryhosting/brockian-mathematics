import Mathlib

/-!
# Abel Ruffini Deg 5
Category: Pure Mathematics
Target: Math.abel_ruffini_deg5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
The development below follows the classical Galois-theoretic argument: the quintic
`X ^ 5 - 4 * X + 2` is irreducible over `ℚ` (Eisenstein at `2`), it has exactly two real roots
and five complex roots, hence its Galois group is the full symmetric group `S₅`, which is not
solvable.  Consequently no complex root of it is expressible by radicals.
-/

namespace Math

open Function Polynomial Polynomial.Gal Ideal

open scoped Polynomial

attribute [local instance] splits_ℚ_ℂ

section Quintic

variable (R : Type*) [CommRing R] (a b : ℕ)

/-- The quintic `X ^ 5 - a * X + b`, over an arbitrary commutative ring. -/

theorem not_solvable_by_rad_quintic (p : ℕ) (x : ℂ) (hx : aeval x (quintic ℚ a b) = 0) (hab : b < a)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) : ¬IsSolvableByRad ℚ x := by
  have h_irred := irreducible_quintic a b p hp hpa hpb hp2b
  exact mt (solvableByRad.isSolvable' h_irred hx) (not_solvable_gal_quintic a b p hab hp hpa hpb hp2b)

end Quintic

/-- **Abel–Ruffini theorem, degree 5.**  There is a monic quintic polynomial over `ℚ` whose
Galois group is not solvable, which has complex roots, and none of whose complex roots is
expressible by radicals over `ℚ`.  (Explicitly, `X ^ 5 - 4 * X + 2`.) -/
