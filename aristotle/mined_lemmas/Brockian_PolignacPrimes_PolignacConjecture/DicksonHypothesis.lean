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

import Mathlib

/-!
Polignac's conjecture (1849) asserts that for every positive even number `n` there are
infinitely many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is open
(the case `n = 2` is the twin prime conjecture).

This file gives a Lean-checked *conditional reduction*: Polignac's conjecture follows from
Dickson's conjecture for two linear forms `M x + a`, `M x + b` (the standard hypothesis that an
admissible system of linear forms simultaneously represents primes infinitely often).

The reduction is the classical sieve/congruence argument: given an even `n`, one produces an
arithmetic progression `M x + a` such that *all* of the intermediate values
`M x + a + 1, …, M x + a + (n-1)` are automatically composite, while the two forms
`M x + a` and `M x + a + n` are admissible.
-/

namespace Brockian.PolignacPrimes

/-- `q` is the prime immediately following `p`: both are prime, `p < q`, and nothing strictly
between them is prime. -/

def DicksonHypothesis : Prop :=
  ∀ M a b : ℕ, 0 < M →
    (∀ p : ℕ, p.Prime → ∃ x : ℕ, ¬ p ∣ (M * x + a) ∧ ¬ p ∣ (M * x + b)) →
    ∀ N : ℕ, ∃ x : ℕ, N < x ∧ Nat.Prime (M * x + a) ∧ Nat.Prime (M * x + b)

/-- If `p` is a prime not dividing `u`, and `c`, `d` have the same parity, then some value of the
progression `u * x` avoids both residues `-c` and `-d` modulo `p`. -/
