/-!
# Goldbach Wheel K 2 1051
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1051
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- Primality, stated in the usual way: `p` is at least `2` and its only divisors are
`1` and `p`. (This file is self-contained, so the predicate is spelled out here.) -/

theorem gwK2Check_range :
    (List.range 1052).all
      (fun n => decide (n < 4) || decide (n % 2 = 1) || gwK2Check n) = true := by
  decide +kernel

/-- **Goldbach Wheel K 2, modulus 1051.**
Every even `n` with `4 ≤ n ≤ 1051` is a sum of two primes. -/
