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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

(The requested header appears at the very top of this file as a plain block comment rather than
as a module docstring, because Lean requires every `import` to precede any module docstring.)

A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` with the same sum of prime
factors counted with multiplicity (`sopfr`), e.g. `(714, 715)`: `714 = 2·3·7·17` and
`715 = 5·11·13`, both with factor sum `29`.

Whether there are infinitely many Ruth–Aaron pairs is an open problem (Erdős conjectured that
there are).  This file contains:

* the basic theory of `sopfr` (additivity, `sopfr n ≤ n`, value at primes);
* verification of the first Ruth–Aaron pairs `5, 8, 15, 77, 125, 714`;
* two *unconditional* partial results: `sopfr n - sopfr (n+1)` is positive infinitely often and
  negative infinitely often, i.e. the difference changes sign infinitely often (a Ruth–Aaron pair
  is exactly a place where the difference vanishes);
* an *unconditional* structural obstruction, `no_prime_semiprime_pair` /
  `not_isRuthAaronPair_of_semiprimes`: no Ruth–Aaron pair consists of two semiprimes, i.e.
  `p * q + 1 = r * s` together with `p + q = r + s` is impossible for primes `p, q, r, s`
  (this rules out the simplest conceivable parametric families);
* a *conditional reduction*: `RuthAaronInfinitude` derives the infinitude of Ruth–Aaron pairs
  from `PrimeFactorizationHypothesis`, a statement phrased purely in terms of lists of primes
  (arbitrarily large products of primes `L` whose product is one less than the product of a list
  `M` of primes with the same sum), with no reference to the factorization function.
  `ruthAaron_infinite_iff` shows that the reduction loses nothing: the hypothesis is in fact
  equivalent to the infinitude statement.
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity.
By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem no_prime_semiprime_pair {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (h1 : p * q + 1 = r * s) (h2 : p + q = r + s) : False := by
  have h1' : (p : ℤ) * q + 1 = (r : ℤ) * s := by exact_mod_cast h1
  have h2' : (p : ℤ) + q = (r : ℤ) + s := by exact_mod_cast h2
  have H : ((p : ℤ) - q) ^ 2 = ((r : ℤ) - s) ^ 2 + 4 := by
    linear_combination ((p : ℤ) + q + r + s) * h2' - 4 * h1'
  have HN : (((p : ℤ) - q).natAbs) ^ 2 = (((r : ℤ) - s).natAbs) ^ 2 + 4 := by
    zify [Int.natAbs_sq, sq_abs]
    simpa [Int.natAbs_sq, sq_abs] using H
  obtain ⟨hU, hV⟩ := sq_eq_sq_add_four HN
  have hrs : r = s := by
    have : ((r : ℤ) - s) = 0 := Int.natAbs_eq_zero.mp hV
    omega
  subst hrs
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  have key : (p = r - 1 ∧ q = r + 1) ∨ (q = r - 1 ∧ p = r + 1) := by omega
  have hrp1 : (r + 1).Prime := by
    rcases key with ⟨_, h4⟩ | ⟨_, h4⟩
    · exact h4 ▸ hq
    · exact h4 ▸ hp
  have hr2' : r = 2 := by
    rcases Nat.even_or_odd r with he | ho
    · exact (Nat.Prime.even_iff hr).mp he
    · have he2 : Even (r + 1) := ho.add_one
      have := (Nat.Prime.even_iff hrp1).mp he2
      omega
  subst hr2'
  rcases key with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega

/-- No Ruth–Aaron pair `(n, n+1)` has both `n` and `n + 1` a product of exactly two primes. -/
