import Mathlib
import RequestProject.GoldbachWheelK2_1051

/-!
# Bridge: the import-free primality predicate agrees with `Nat.Prime`

`RequestProject/GoldbachWheelK2_1051.lean` is import-free (so that the required header comment
is the first thing in the file) and therefore uses its own definition `Brockian.IsPrime`.
Here we check that this predicate is literally `Nat.Prime`, and restate the main theorem
in Mathlib's vocabulary.
-/

namespace Brockian


theorem GoldbachWheelK2_1051' (m : ℕ) (hm : Even m) (h4 : 4 ≤ m) (hle : m ≤ 2 * 1051) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = m := by
  obtain ⟨p, q, hp, hq, hpq⟩ :=
    GoldbachWheelK2_1051 m (even_iff_two_dvd.mp hm) h4 hle
  exact ⟨p, q, (isPrime_iff_nat_prime p).mp hp, (isPrime_iff_nat_prime q).mp hq, hpq⟩

end Brockian

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Brockian

/-- Primality of a natural number, stated from first principles: `n` is prime when `2 ≤ n`
and its only divisors are `1` and `n`.  (This file is deliberately import-free, so that the
header comment above is the very first thing in the file; `Brockian.isPrime_iff_nat_prime`
in `RequestProject/GoldbachWheelK2_1051_Bridge.lean` shows this agrees with `Nat.Prime`.) -/
