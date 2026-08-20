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
# Hyperperfect Infinitude
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a `/-!` module docstring because Lean 4
-- does not allow any command, including a module docstring, to precede the `import` lines.)

/-
## Overview

A positive integer `n` is *`k`-hyperperfect* (for `k ≥ 1`) when

  `n = 1 + k * (σ(n) - n - 1)`,

where `σ(n)` is the sum of all divisors of `n`; equivalently `σ(n) - n - 1` is the sum of
the divisors of `n` other than `1` and `n`.  Taking `k = 1` recovers the perfect numbers.
To avoid truncated natural subtraction the definition below is stated in the equivalent
subtraction-free form `n + k * (n + 1) = 1 + k * σ(n)`.

Whether there are infinitely many hyperperfect numbers is an open problem: already the case
`k = 1` is the (open) question of whether there are infinitely many perfect numbers.  What is
proved here is therefore a *conditional reduction* together with unconditional supporting
results:

* `Brockian.HyperperfectNumbers.isHyperperfect_mul` — an unconditional construction: whenever
  `k ≥ 1` and both `k + 1` and `k² + k + 1` are prime, the number `(k + 1)(k² + k + 1)` is
  `k`-hyperperfect.  (E.g. `k = 1, 2, 6` give `6`, `21`, `301`.)
* `Brockian.HyperperfectNumbers.HyperperfectInfinitude` — the main target: if there are
  arbitrarily large `k` with `k + 1` and `k² + k + 1` both prime (an instance of Bunyakovsky's
  conjecture), then the set of hyperperfect numbers is infinite.
* `Brockian.HyperperfectNumbers.hyperperfect_infinite_of_infinitely_many_mersenne_primes` — a
  second, independent conditional reduction: infinitely many Mersenne primes also imply
  infinitely many hyperperfect numbers (via the even perfect numbers, which are
  `1`-hyperperfect).
-/

import Mathlib

open scoped ArithmeticFunction.sigma
open ArithmeticFunction

namespace Brockian.HyperperfectNumbers

/-- `n` is `k`-hyperperfect: `k ≥ 1`, `n > 1` and `n = 1 + k * (σ n - n - 1)`, written in the
subtraction-free form `n + k * (n + 1) = 1 + k * σ n`. -/

theorem hyperperfect_twentyone : Hyperperfect 21 :=
  ⟨2, by simpa using isHyperperfect_mul (k := 2) two_pos (by norm_num) (by norm_num)⟩

/-- `301` is a `6`-hyperperfect number. -/
