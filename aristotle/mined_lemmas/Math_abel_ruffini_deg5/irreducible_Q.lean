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

theorem irreducible_Q : Irreducible (Q ℚ) := by
  rw [← map_Q (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion
    · exact (Ideal.span_singleton_prime (by norm_num : (2 : ℤ) ≠ 0)).mpr Int.prime_two
    · rw [(monic_Q ℤ).leadingCoeff, mem_span_singleton]
      norm_num
    · intro n hn
      rw [mem_span_singleton]
      rw [degree_Q] at hn
      norm_cast at hn
      interval_cases n <;> simp [Q, coeff_X_pow, coeff_X]
    · simp only [degree_Q, ← WithBot.coe_zero]
      decide
    · rw [span_singleton_pow, mem_span_singleton]
      simp [Q, coeff_X_pow]
  all_goals exact (monic_Q ℤ).isPrimitive

set_option maxHeartbeats 1000000 in
/-- `X ^ 5 - 4 * X + 2` has at most three real roots: two applications of Rolle's theorem
reduce this to the fact that its second derivative `20 * X ^ 3` has a single root. -/
