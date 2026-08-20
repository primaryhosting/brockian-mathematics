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
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`
-- because Lean 4 requires `import` commands to precede every other command, including
-- module docstrings.)

import Mathlib

/-!
# Polignac Conjecture

De Polignac's conjecture states that for every positive even number `n` there are infinitely
many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is an open problem (the case
`n = 2` is the twin prime conjecture), so what is proved here is a *conditional reduction*:
Polignac's conjecture is derived from Dickson's conjecture on simultaneous primality of
linear forms.

The derivation is the classical one.  Given an even `n ≥ 2`, one chooses for each `j` with
`0 < j < n` a distinct prime `q j > n`, sets `Q = ∏ q j` and uses the Chinese Remainder Theorem
to find `a` with `q j ∣ a + j` for all such `j`.  The pair of linear forms `a + Q x`,
`(a + n) + Q x` is then admissible, so Dickson's conjecture produces arbitrarily large `x`
making both forms prime; and every intermediate value `a + Q x + j` (`0 < j < n`) is divisible
by the prime `q j`, which is smaller than it, hence composite.  So the two primes are
consecutive with difference exactly `n`.
-/

namespace Brockian
namespace PolignacPrimes

open Finset
open scoped Function

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies strictly
between them. -/

def IsConsecutivePrimePair (p q : ℕ) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ ∀ r, p < r → r < q → ¬ Nat.Prime r

/-- **Dickson's conjecture**: a finite family of linear forms `a i + b i * x` with positive
leading coefficients which is *admissible* (for every prime `r` there is an `x` making none of
the values divisible by `r`) takes simultaneously prime values for arbitrarily large `x`. -/
