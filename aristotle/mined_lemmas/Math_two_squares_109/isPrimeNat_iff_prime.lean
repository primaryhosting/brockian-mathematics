/-!
# Two Squares 109
Category: Pure Mathematics
Target: Math.two_squares_109
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- Primality of a natural number, stated elementarily: `n` is at least `2` and its only
proper divisor is `1`.  (See `Math.isPrimeNat_iff_prime` in `RequestProject.MathMathlib`
for the proof that this agrees with Mathlib's `Nat.Prime`.) -/

theorem isPrimeNat_iff_prime (n : ℕ) : IsPrimeNat n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨hn, h⟩
    refine Nat.prime_def.mpr ⟨hn, fun m hm => ?_⟩
    rcases lt_or_eq_of_le (Nat.le_of_dvd (by omega) hm) with hlt | heq
    · exact Or.inl (h m hlt hm)
    · exact Or.inr heq
  · intro hp
    refine ⟨hp.two_le, fun m hm hmd => ?_⟩
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp m hmd) with h | h
    · exact h
    · omega

/-- `109` is prime, in Mathlib's sense. -/
