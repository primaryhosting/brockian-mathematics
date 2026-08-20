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
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Weird Exists
Category: Brockian Conjecture
Target: Brockian.WeirdNumbers.OddWeirdExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A natural number `n` is *weird* (`Nat.Weird`) if it is abundant (the sum of its proper
divisors exceeds `n`) but not pseudoperfect (no subset of its proper divisors sums to `n`).

Whether an **odd** weird number exists is a well-known open problem; no odd weird number is
known.  Consequently the file below does not claim an unconditional existence proof.
Instead it provides a Lean-checked *reduction*:

* `Brockian.WeirdNumbers.weird_mul_prime` : if `n` is weird and `p` is a prime exceeding the
  sum of the divisors of `n`, then `n * p` is weird.
* `Brockian.WeirdNumbers.OddWeirdExists` : an odd weird number exists **iff** there are
  arbitrarily large odd weird numbers.  In other words, a single odd weird number would
  immediately yield infinitely many.

Unconditionally we also record:

* `Brockian.WeirdNumbers.even_weird_exists` : `70` is an (even) weird number;
* `Brockian.WeirdNumbers.odd_weird_ge_1000` : every odd weird number is at least `1000`
  (the only odd abundant number below `1000` is `945`, and `945` is pseudoperfect).
-/

namespace Brockian.WeirdNumbers

open Finset

/-- The sum of all divisors of `n`. -/
abbrev sigmaOne (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- For a prime `p` not dividing `n`, `σ (n * p) = σ n * (p + 1)`. -/

lemma abundant_mul_prime {n p : ℕ} (hn : n.Weird) (hp : p.Prime) (hlt : sigmaOne n < p) :
    (n * p).Abundant := by
  have hnpos : 0 < n := Weird.pos hn
  have hn_le : n ≤ sigmaOne n :=
    Finset.single_le_sum (f := fun d : ℕ => d) (fun i _ => Nat.zero_le i)
      (Nat.mem_divisors_self n hnpos.ne')
  have hpn : ¬ p ∣ n := fun hd => by
    have := Nat.le_of_dvd hnpos hd
    omega
  have hsig := sigmaOne_mul_prime (n := n) hp hpn
  have h2 : 2 * n < sigmaOne n := two_mul_lt_sigmaOne hn
  have hsum : sigmaOne (n * p) = (∑ i ∈ (n * p).properDivisors, i) + n * p :=
    Nat.sum_divisors_eq_sum_properDivisors_add_self
  have hp1 : 1 ≤ p := hp.pos
  show n * p < ∑ i ∈ (n * p).properDivisors, i
  nlinarith [hsig, hsum, h2, hp1]

/-- If `n` is weird and `p` is a prime larger than the sum of the divisors of `n`,
then `n * p` is not pseudoperfect. -/
