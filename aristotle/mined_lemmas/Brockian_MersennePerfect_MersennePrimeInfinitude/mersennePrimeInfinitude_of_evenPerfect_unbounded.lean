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

import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
*Lean-checked reduction*: the statement is shown to be equivalent to the infinitude of even
perfect numbers, via the Euclid–Euler correspondence `p ↦ 2 ^ (p - 1) * (2 ^ p - 1)`.

The target declaration `Brockian.MersennePerfect.MersennePrimeInfinitude` is therefore a
conditional theorem: *if* there are infinitely many even perfect numbers, *then* there are
infinitely many Mersenne primes.  The converse implication, and the resulting equivalence, are
also proved, as is a contrapositive/boundedness reformulation.
-/

namespace Brockian.MersennePerfect

open scoped Nat

/-- The set of exponents `p` for which `2 ^ p - 1` is a (Mersenne) prime.  Such a `p` is
automatically prime itself (see `mersenneExponents_eq`). -/

theorem mersennePrimeInfinitude_of_evenPerfect_unbounded
    (h : ∀ N : ℕ, ∃ n, Even n ∧ Nat.Perfect n ∧ N < n) :
    {p : ℕ | Nat.Prime p ∧ Nat.Prime (2 ^ p - 1)}.Infinite := by
  refine MersennePrimeInfinitude ?_
  have h5 : ∀ N : ℕ, ∃ n ∈ evenPerfects, N < n := by
    intro N
    obtain ⟨n, hev, hperf, hN⟩ := h N
    exact ⟨n, ⟨hev, hperf⟩, hN⟩
  exact (mersenne_infinitude_tfae.out 4 2).1 h5

/-! ### An unconditional partial result

While the infinitude of Mersenne *primes* is open, one can prove unconditionally that infinitely
many primes occur as divisors of Mersenne numbers `2 ^ p - 1` with `p` prime: any prime divisor
`q` of `2 ^ p - 1` (with `p` prime) satisfies `q ≡ 1 [MOD p]`, hence `p < q`. -/

/-- Any prime divisor of `2 ^ p - 1`, for `p` prime, exceeds `p`. -/
