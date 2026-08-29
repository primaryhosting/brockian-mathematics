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

theorem degree_quintic : (quintic R a b).degree = ((5 : ℕ) : WithBot ℕ) := by
  suffices degree (X ^ 5 - C (a : R) * X) = ((5 : ℕ) : WithBot ℕ) by
    rwa [quintic, degree_add_eq_left_of_degree_lt]
    convert (degree_C_le (R := R)).trans_lt (WithBot.coe_lt_coe.mpr (show 0 < 5 by simp))
  rw [degree_sub_eq_left_of_degree_lt] <;> rw [degree_X_pow]
  exact (degree_C_mul_X_le (a : R)).trans_lt (WithBot.coe_lt_coe.mpr (show 1 < 5 by simp))

