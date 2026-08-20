/-
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The binary (`K = 2`) Goldbach property: `n` is a sum of two primes. -/

theorem goldbachK2_of_sub_prime (n p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (n - p))
    (hpn : p ≤ n) : GoldbachK2 n :=
  ⟨p, n - p, hp, hq, by omega⟩

set_option maxHeartbeats 4000000 in
/-- **Goldbach wheel, `K = 2`, modulus `1051`.**
Every even number `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
