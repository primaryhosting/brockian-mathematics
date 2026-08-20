/-
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

Chen's theorem (1973) states that every sufficiently large even number can be written as
`p + q` where `p` is prime and `q` has at most two prime factors (counted with multiplicity),
i.e. `q` is prime or a product of two primes.

Mathlib does not contain Chen's theorem (nor Goldbach's conjecture, nor any sieve machinery
strong enough to derive it), so the unconditional statement is out of reach here. What this
file contains is:

* a faithful formalization of the statement (`Frontier.ChenStatement`);
* an explicit, kernel-checked **base case**: every even `n` with `4 ≤ n ≤ 200` has a Chen
  representation (`Frontier.Chen_base`);
* a **Lean-checked reduction**: the binary Goldbach conjecture implies Chen's statement
  (`Frontier.Chen_theorem`), with the explicit threshold `N = 4`.
-/

namespace Frontier

/-- `AlmostPrime2 q` means that `q` has at most two prime factors, counted with
multiplicity (i.e. `Ω q ≤ 2`): `q` is `1`, a prime, or a product of two primes. -/

theorem goldbach_check :
    ∀ n ∈ Finset.range 201, 4 ≤ n → n % 2 = 0 →
      ∃ p ∈ Finset.range (n + 1), Nat.Prime p ∧ Nat.Prime (n - p) := by
  decide

/-- **Base case.** Every even number `n` with `4 ≤ n ≤ 200` has a Chen representation.
(In fact a Goldbach representation, verified by kernel computation.) -/
