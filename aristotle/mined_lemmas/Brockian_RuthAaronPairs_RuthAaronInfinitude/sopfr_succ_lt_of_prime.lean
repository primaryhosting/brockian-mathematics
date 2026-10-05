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

lemma sopfr_succ_lt_of_prime {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p) : sopfr (p + 1) < sopfr p := by
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have h2 : 2 ∣ p + 1 := by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
  have := sopfr_lt_of_even (n := p + 1) (by omega) h2
  rw [sopfr_prime hp]
  omega

/-- If `n + 1` is prime then `sopfr n < sopfr (n+1)`, so `(n, n+1)` is not a Ruth–Aaron pair. -/
