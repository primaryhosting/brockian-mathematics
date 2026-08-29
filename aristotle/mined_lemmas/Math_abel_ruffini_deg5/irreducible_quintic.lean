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

theorem irreducible_quintic (p : ℕ) (hp : p.Prime) (hpa : p ∣ a) (hpb : p ∣ b) (hp2b : ¬p ^ 2 ∣ b) :
    Irreducible (quintic ℚ a b) := by
  rw [← map_quintic a b (Int.castRingHom ℚ), ← IsPrimitive.Int.irreducible_iff_irreducible_map_cast]
  on_goal 1 =>
    apply irreducible_of_eisenstein_criterion
    · rwa [span_singleton_prime (Int.natCast_ne_zero.mpr hp.ne_zero), Int.prime_iff_natAbs_prime]
    · rw [leadingCoeff_quintic, mem_span_singleton]
      exact mod_cast mt Nat.dvd_one.mp hp.ne_one
    · intro n hn
      rw [mem_span_singleton]
      rw [degree_quintic] at hn; norm_cast at hn
      interval_cases n <;>
      simp +decide only [quintic, coeff_X_pow, coeff_C, Int.natCast_dvd_natCast.mpr,
        hpb, if_true, coeff_C_mul, if_false, coeff_X_zero, hpa, coeff_add, zero_add, mul_zero,
        coeff_sub, add_zero, zero_sub, dvd_neg, neg_zero, dvd_mul_of_dvd_left]
    · simp only [degree_quintic, ← WithBot.coe_zero]
      decide
    · rw [coeff_zero_quintic, span_singleton_pow, mem_span_singleton]
      exact mt Int.natCast_dvd_natCast.mp hp2b
  all_goals exact Monic.isPrimitive (monic_quintic a b)

attribute [local simp] map_ofNat in -- use `ofNat` simp theorem with bad keys
