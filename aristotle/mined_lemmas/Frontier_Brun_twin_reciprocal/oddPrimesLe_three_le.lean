import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma oddPrimesLe_three_le {z p : ℕ} (hp : p ∈ oddPrimesLe z) : 3 ≤ p := by
  have h2 := (oddPrimesLe_prime hp).two_le
  have h3 := oddPrimesLe_ne_two hp
  omega

end Brun

import RequestProject.Brun.Counting
import RequestProject.Brun.Bonferroni
import RequestProject.Brun.PrimeSums

/-!
# Brun's sieve

The main result is `Brun.twinCount_le`, an explicit upper bound for the number of `n < N`
such that `n` and `n + 2` are both prime, in terms of a sieve level `z` and an even
truncation level `k`.
-/

namespace Brun

open Finset

/-! ### Alternating sums over subsets -/

