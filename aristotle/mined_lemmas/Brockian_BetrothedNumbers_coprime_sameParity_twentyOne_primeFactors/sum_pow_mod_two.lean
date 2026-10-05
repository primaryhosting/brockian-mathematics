/-
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Coprime Same Parity Twenty One Prime Factors
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.coprime_sameParity_twentyOne_primeFactors
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

/-!
## Betrothed (quasi-amicable) numbers

A pair `(m, n)` of positive integers is *betrothed* (or *quasi-amicable*) when each of the two
numbers is the sum of the **non-trivial** divisors of the other, i.e.

`σ(m) = σ(n) = m + n + 1`.

This file formalizes the second half of Proposition 2 of Hagis and Lord, *Quasi-amicable numbers*
(Math. Comp. 31 (1977)): if the two members of a betrothed pair are **coprime** and have the
**same parity**, then both are odd (indeed both are perfect squares) and the product `m * n` has
at least twenty-one distinct prime factors.

The proof is completely elementary:

* both members are odd, since two coprime numbers cannot both be even;
* therefore `σ(m) = m + n + 1` is odd, so `m` (and likewise `n`) is a perfect square, by
  `Brockian.BetrothedNumbers.odd_sigma_one_iff`;
* by coprimality `σ(mn) = σ(m)σ(n) = (m + n + 1)^2 > 4mn`, so the odd number `N = mn` has
  abundancy `σ(N)/N > 4`;
* the abundancy of `N` is bounded above by `∏_{p ∣ N} p/(p-1)`, and the product of `p/(p-1)`
  over any twenty distinct odd primes is at most the value taken over the twenty smallest odd
  primes `3, 5, …, 73`, which is `< 4`.

Hence `ω(mn) ≥ 21`. This bound is exactly what is proved here; it is a *theorem*, and should be
distinguished from the (much larger) **computational** lower bounds that appear in the
literature, which rest on extensive machine search rather than on proof. Such historical
numerical records — e.g. that no coprime betrothed pair of the same parity is known at all, and
that searches have ruled out all such pairs below various large bounds — are deliberately **not**
stated as Lean theorems anywhere in this file; only the unconditional inequality `21 ≤ ω(mn)` is.
-/

namespace Brockian.BetrothedNumbers

open Finset ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- A *betrothed* (quasi-amicable) pair: `σ m = σ n = m + n + 1`, i.e. each number is the sum of
the non-trivial divisors (excluding `1` and the number itself) of the other. -/

lemma sum_pow_mod_two {p : ℕ} (hp : Odd p) (m : ℕ) :
    (∑ i ∈ Finset.range m, p ^ i) % 2 = m % 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.mp hp.pow]
      omega

/-- An odd number has odd sum of divisors exactly when it is a perfect square. -/
