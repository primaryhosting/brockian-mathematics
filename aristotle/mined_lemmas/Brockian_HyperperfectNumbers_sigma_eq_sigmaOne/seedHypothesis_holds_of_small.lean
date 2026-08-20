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
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hyperperfect All K
Category: Brockian Conjecture
Target: Brockian.HyperperfectNumbers.HyperperfectAllK
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A natural number `n` is *`k`-hyperperfect* when `n = 1 + k * (σ n - n - 1)`, where `σ` is the
sum-of-divisors function.  For `k = 1` these are exactly the perfect numbers.  The conjecture
addressed here states that **for every `k ≥ 1` there exists a `k`-hyperperfect number**; this is
an open problem (no `5`-hyperperfect number is known, for instance).

This file contains:

* the basic theory (`sigma`, `IsHyperperfect`, and the usual integer form of the equation);
* an exact characterisation of the hyperperfect numbers of the shape `m * q` with `q` a prime not
  dividing `m` (`isHyperperfect_mul_prime_iff`), and the resulting construction
  (`isHyperperfect_of_seed`);
* the classical semiprime family: if `k + 1` and `k ^ 2 + k + 1` are prime then
  `(k + 1) * (k ^ 2 + k + 1)` is `k`-hyperperfect (`isHyperperfect_classical`), together with the
  full semiprime characterisation `(p - k) * (q - k) = k ^ 2 + 1`;
* unconditional witnesses for a number of small `k` (`exists_hyperperfect_of_small`);
* the main target `HyperperfectAllK`: a Lean-checked reduction of the conjecture to the
  arithmetic hypothesis `SeedHypothesis`.
-/

namespace Brockian.HyperperfectNumbers

open Finset

/-- `sigma n` is the sum of the (positive) divisors of `n`, usually written `σ(n)`. -/

theorem seedHypothesis_holds_of_small {k : ℕ}
    (hk : k ∈ ({1, 2, 3, 4, 6, 10, 11, 12, 18, 19} : Finset ℕ)) :
    ∃ m q : ℕ, 1 < m ∧ q.Prime ∧ ¬ q ∣ m ∧
      k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k := by
  have key : ∀ (m q : ℕ), 1 < m → q.Prime → ¬ q ∣ m → IsHyperperfect k (m * q) →
      ∃ m q : ℕ, 1 < m ∧ q.Prime ∧ ¬ q ∣ m ∧
        k * sigma m * (q + 1) + 1 = m * q * (1 + k) + k := by
    intro m q hm hq hqm h
    exact ⟨m, q, hm, hq, hqm, (isHyperperfect_mul_prime_iff hm hq hqm).mp h⟩
  fin_cases hk
  · exact key 2 3 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_1_6)
  · exact key 3 7 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_2_21)
  · exact key 25 13 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_3_325)
  · exact key 625 3121 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_4_1950625)
  · exact key 7 43 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_6_301)
  · exact key 121 1321 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_10_159841)
  · exact key 289 37 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_11_10693)
  · exact key 17 41 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_12_697)
  · exact key 31 43 (by norm_num) (by norm_num) (by decide) (by simpa using isHyperperfect_18_1333)
  · exact key 841 61 (by norm_num) (by norm_num) (by decide)
      (by simpa using isHyperperfect_19_51301)

/-- **Brockian conjecture (hyperperfect numbers, all `k`), conditional form.**

The conjecture asserts that for every `k ≥ 1` there exists a `k`-hyperperfect number; this is an
open problem.  The theorem below is a Lean-checked reduction: it derives the conjecture from the
arithmetic hypothesis `SeedHypothesis`, i.e. from the solvability, for each `k ≥ 1`, of
`k * σ m * (q + 1) + 1 = m * q * (1 + k) + k` in a seed `m > 1` and a prime `q ∤ m`.  The
resulting `k`-hyperperfect number is `m * q`.

Unconditional instances are provided by `exists_hyperperfect_of_small`. -/
