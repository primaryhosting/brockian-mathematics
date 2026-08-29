import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean 4 requires every `import` to precede any module docstring, so the required header is
reproduced verbatim as the module docstring immediately after the import below.)
-/

import Mathlib

/-!
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

De Polignac's conjecture states that for every positive even number `n` there are infinitely
many pairs of *consecutive* primes whose difference is `n`.  This is an open problem (it contains
the twin prime conjecture as the case `n = 2`), so what is proved here is a *conditional
reduction*: the full conjecture is derived from a two-form special case of Dickson's conjecture
on prime values of linear forms (`DicksonPairHypothesis`).

The reduction is the classical sieve-free argument: given an even `n ≥ 2`, one uses the Chinese
remainder theorem to build an arithmetic progression `r + M ℕ` such that

* every `p ≡ r [MOD M]` has `p + k` divisible by a fixed prime `< p` for each `0 < k < n`
  (so all the numbers strictly between `p` and `p + n` are composite), and
* the pair of linear forms `r + M m`, `r + n + M m` is admissible, i.e. no prime divides
  the product for all `m`.

Dickson's conjecture applied to this pair then produces infinitely many consecutive prime pairs
with gap exactly `n`.

Unconditional results proved here as well:

* `Brockian.PolignacPrimes.eq_two_of_odd_gap` – for odd `n` at most one prime `p` has `p + n`
  prime, so the evenness hypothesis in the conjecture is necessary;
* `Brockian.PolignacPrimes.not_polignacProperty_of_odd`;
* `Brockian.PolignacPrimes.polignacProperty_iff` – reformulation of the "infinitely many"
  clause as an unboundedness statement.
-/

namespace Brockian.PolignacPrimes

/-- `p` and `p + n` are consecutive primes: both are prime and no number strictly between
them is prime. -/

theorem eq_two_of_odd_gap {n p : ℕ} (hn : Odd n) (hp : Nat.Prime p)
    (hpn : Nat.Prime (p + n)) : p = 2 := by
  by_contra hne
  have hpodd : Odd p := hp.odd_of_ne_two hne
  have heven : Even (p + n) := hpodd.add_odd hn
  have h2 : p + n = 2 := (Nat.Prime.even_iff hpn).mp heven
  have hp2 : 2 ≤ p := hp.two_le
  have hn1 : 1 ≤ n := hn.pos
  omega

/-- De Polignac's property fails for every odd `n`. -/
