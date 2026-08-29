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

theorem gal_quintic (hab : b < a) (h_irred : Irreducible (quintic ℚ a b)) :
    Bijective (galActionHom (quintic ℚ a b) ℂ) := by
  apply galActionHom_bijective_of_prime_degree' h_irred
  · simp only [natDegree_quintic]; decide
  · rw [complex_roots_quintic a b h_irred.separable, Nat.succ_le_succ_iff]
    exact (real_roots_quintic_le a b).trans (Nat.le_succ 3)
  · simp_rw [complex_roots_quintic a b h_irred.separable, Nat.succ_le_succ_iff]
    exact real_roots_quintic_ge a b hab

/-- The Galois group of `X ^ 5 - a * X + b` (with `b < a` and Eisenstein at `p`) is not
solvable. -/
