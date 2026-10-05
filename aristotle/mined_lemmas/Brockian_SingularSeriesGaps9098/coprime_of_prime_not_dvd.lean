/-!
# Singular Series Gaps 9098
Category: Brockian Corpus
Target: Brockian.SingularSeriesGaps9098
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained (it uses no imports at all), so that the
required header comment can literally be the first thing in the file.  Everything below is
built from the Lean 4 core library only.
-/

namespace Brockian

/-! ## Primality, admissible gap patterns -/

/-- Primality, spelled out from first principles: `p` is at least `2` and its only divisors
are `1` and `p`. -/

theorem coprime_of_prime_not_dvd {p m : Nat} (hp : IsPrime p) (h : ¬ p ∣ m) :
    Nat.Coprime p m := by
  have hl := Nat.gcd_dvd_left p m
  have hr := Nat.gcd_dvd_right p m
  rcases hp.2 _ hl with h3 | h3
  · exact h3
  · exact absurd (h3 ▸ hr) h

/-! ## A family of admissible gap patterns -/

/-- The arithmetic-progression gap pattern `{0, M, 2M, …, (k-1)M}`, viewed as a set of shifts
inside the range `[0, (k-1)M]`. -/
