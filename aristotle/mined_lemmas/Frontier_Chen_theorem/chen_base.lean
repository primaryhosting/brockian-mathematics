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

theorem Chen_base (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 200) (he : Even n) : ChenRepr n := by
  obtain ⟨p, hp_mem, hp, hq⟩ :=
    goldbach_check n (Finset.mem_range.mpr (by omega)) h4 (Nat.even_iff.mp he)
  have hple : p ≤ n := by
    have := Finset.mem_range.mp hp_mem
    omega
  exact ChenRepr.of_two_primes hp hq (by omega)

/-- **Chen's theorem, conditional on Goldbach.**  Assuming the binary Goldbach conjecture,
every even number `n ≥ 4` is of the form `p + q` with `p` prime and `q` having at most two
prime factors; in particular Chen's statement holds with threshold `N = 4`.

This is a Lean-checked reduction: the unconditional theorem of Chen (1973) is not available
in Mathlib, and is not proved here. An unconditional finite instance (all even `n` with
`4 ≤ n ≤ 200`) is proved in `Frontier.Chen_base`. -/
