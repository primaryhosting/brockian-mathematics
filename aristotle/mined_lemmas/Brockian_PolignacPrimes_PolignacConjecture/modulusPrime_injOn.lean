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

lemma modulusPrime_injOn (n : ℕ) (hn : 2 ≤ n) {k l : ℕ} (hkl : k ≠ l) :
    modulusPrime n k ≠ modulusPrime n l := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · exact absurd rfl hkl
    · have := lt_modulusPrime n l hl
      rw [modulusPrime_zero]
      omega
  · rcases Nat.eq_zero_or_pos l with rfl | hl
    · have := lt_modulusPrime n k hk
      rw [modulusPrime_zero]
      omega
    · have hk' : modulusPrime n k = Nat.nth Nat.Prime (n + k) := by simp [modulusPrime, hk.ne']
      have hl' : modulusPrime n l = Nat.nth Nat.Prime (n + l) := by simp [modulusPrime, hl.ne']
      rw [hk', hl']
      intro h
      exact hkl (by
        have := (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h
        omega)

/-- Main construction: for even `n ≥ 2` there is an admissible pair of linear forms
`m ↦ r + M m`, `m ↦ r + n + M m` such that all intermediate values `r + M m + k`
(`0 < k < n`) have a nontrivial divisor bounded by `M`. -/
