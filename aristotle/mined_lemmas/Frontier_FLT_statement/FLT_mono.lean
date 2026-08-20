/-
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# FLT Statement
Category: Frontier — Prime Numbers
Target: Frontier.FLT_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- Fermat's Last Theorem for a fixed exponent `n`, stated with positive integers:
`x ^ n + y ^ n = z ^ n` has no solution with `x, y, z > 0`. -/

theorem FLT_mono {m n : ℕ} (hmn : m ∣ n) (hm : FLTFor m) : FLTFor n :=
  (FLTFor_iff_fermatLastTheoremFor n).2
    (((FLTFor_iff_fermatLastTheoremFor m).1 hm).mono hmn)

/-- **Formal statement of Fermat's Last Theorem, together with a Lean-checked reduction
to the case of odd prime exponents.**

`x ^ n + y ^ n = z ^ n` has no positive-integer solution for `n > 2` **if and only if** it has
no positive-integer solution for every odd prime exponent `p`.

The nontrivial (←) direction is the classical reduction: every `n > 2` is divisible by `4` or by
an odd prime, and the case `n = 4` is Fermat's descent
(Mathlib's `FermatLastTheorem.of_odd_primes` and `fermatLastTheoremFour`). -/
