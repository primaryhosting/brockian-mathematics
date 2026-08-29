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

theorem mersenne_infinitude_tfae :
    List.TFAE [mersennePrimes.Infinite,
      mersenneExponents.Infinite,
      evenPerfects.Infinite,
      (∀ N : ℕ, ∃ p ∈ mersenneExponents, N < p),
      (∀ N : ℕ, ∃ n ∈ evenPerfects, N < n)] := by
  tfae_have 1 ↔ 2 := mersennePrimes_infinite_iff
  tfae_have 2 ↔ 3 := mersenneExponents_infinite_iff
  tfae_have 2 ↔ 4 := mersenneExponents_infinite_iff_unbounded
  tfae_have 3 → 5 := by
    intro h N
    obtain ⟨n, hn, hNn⟩ := h.exists_gt N
    exact ⟨n, hn, hNn⟩
  tfae_have 5 → 3 := Set.infinite_of_forall_exists_gt
  tfae_finish

/-! ### A Lucas–Lehmer sufficient criterion -/

/-- If infinitely many exponents `p > 1` pass the Lucas–Lehmer test, then there are infinitely
many Mersenne primes.  (Mathlib provides sufficiency of the Lucas–Lehmer test.) -/
