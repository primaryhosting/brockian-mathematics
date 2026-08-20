import Mathlib
import RequestProject.GoldbachWheelK2_727

/-!
# Goldbach Wheel K 2 727 — Mathlib restatement

The target theorem `Brockian.GoldbachWheelK2_727` is stated in a self-contained way (its own
primality predicate `Brockian.IsPrime`), because the required file header must be the very first
thing in that file and Lean does not accept `import` after it.  Here we bridge that predicate to
`Nat.Prime` and restate the result in Mathlib terms.
-/

namespace Brockian


theorem GoldbachWheelK2_727_natPrime (n : ℕ) (h4 : 4 ≤ n) (h727 : n ≤ 727) (hev : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := GoldbachWheelK2_727 n h4 h727 (Nat.even_iff.mp hev)
  exact ⟨p, q, nat_prime_iff_isPrime.mpr hp, nat_prime_iff_isPrime.mpr hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality of a natural number, in the usual sense: `p` is at least `2` and its only
divisors are `1` and `p`. -/
