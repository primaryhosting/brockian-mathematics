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

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
A *Ruth–Aaron pair* is a pair of consecutive integers `(n, n+1)` whose sums of prime
factors, counted with multiplicity, agree; the name comes from the pair `(714, 715)`.
Whether there are infinitely many such pairs is an open problem (Erdős); the file below
develops the basic theory of the function `sopfr`, proves a number of unconditional
structural results about Ruth–Aaron pairs, and gives the infinitude statement as a
conditional reduction from the unboundedness hypothesis.
-/

namespace Brockian
namespace RuthAaronPairs

/-! ## The sum-of-prime-factors function `sopfr` -/

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(OEIS A001414).  By convention `sopfr 0 = sopfr 1 = 0`. -/

theorem infinitely_many_sign_changes :
    {n : ℕ | sopfr n < sopfr (n + 1) ∧ sopfr (n + 2) < sopfr (n + 1)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes (max (N + 2) 7)
  have h7 : 7 ≤ p := le_trans (le_max_right _ _) hpN
  have hN : N + 2 ≤ p := le_trans (le_max_left _ _) hpN
  have hp1 : p - 1 + 1 = p := by omega
  have hp2 : p - 1 + 2 = p + 1 := by omega
  refine ⟨p - 1, ⟨sopfr_lt_of_succ_prime (n := p - 1) (by rwa [hp1]), ?_⟩, by omega⟩
  rw [hp1, hp2]
  exact sopfr_succ_lt_of_prime hp h7

/-! ## Infinitude -/

/-- The Ruth–Aaron unboundedness hypothesis: there are Ruth–Aaron pairs beyond every bound.
This is the (open) conjecture of Erdős that Ruth–Aaron pairs never stop occurring. -/
