import Mathlib
import RequestProject.GoldbachWheelK2_947

/-!
Companion file: certifies that the self-contained primality predicate
`Brockian.IsPrime` used in `RequestProject/GoldbachWheelK2_947.lean` coincides with
Mathlib's `Nat.Prime`, and restates the main theorem in Mathlib terms.
-/

namespace Brockian


theorem isPrime_iff_nat_prime (n : Nat) : IsPrime n ↔ Nat.Prime n := by
  constructor
  · rintro ⟨h2, h⟩
    refine Nat.prime_def_lt.mpr ⟨h2, ?_⟩
    intro m hmn hdvd
    exact h m hmn hdvd
  · intro hp
    exact ⟨hp.two_le, fun m hmn hdvd => (Nat.prime_def_lt.mp hp).2 m hmn hdvd⟩

/-- Mathlib restatement of `Brockian.GoldbachWheelK2_947`: every even `n` with
`4 ≤ n ≤ 2 * 947` is a sum of two primes. -/
