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

theorem ChenRepr.of_two_primes {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : n = p + q) : ChenRepr n :=
  ⟨p, q, hp, AlmostPrime2.of_prime hq, h⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Kernel-checked Goldbach verification for all even `n` with `4 ≤ n ≤ 200`. -/
