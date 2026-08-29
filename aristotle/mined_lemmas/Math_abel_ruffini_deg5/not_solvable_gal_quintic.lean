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

theorem not_solvable_gal_quintic (p : ℕ) (hab : b < a)
    (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    ¬ IsSolvable (quintic ℚ a b).Gal := by
  have h_irred := irreducible_quintic a b p hp hpa hpb hp2b
  intro h
  refine Equiv.Perm.not_solvable _ (le_of_eq ?_)
    (solvable_of_surjective (gal_quintic a b hab h_irred).2)
  rw_mod_cast [Cardinal.mk_fintype, complex_roots_quintic a b h_irred.separable]

