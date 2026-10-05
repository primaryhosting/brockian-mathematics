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

lemma no_three_consecutive_primes {p : ℕ} (hp : p.Prime) (h1 : (p + 1).Prime)
    (h2 : (p + 2).Prime) : False := by
  rcases Nat.even_or_odd p with he | ho
  · have hp2 : p = 2 := (Nat.Prime.even_iff hp).mp he
    subst hp2
    norm_num at h2
  · have he1 : Even (p + 1) := by
      rcases ho with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩
    have h3 : p + 1 = 2 := (Nat.Prime.even_iff h1).mp he1
    have h4 : p = 1 := by omega
    subst h4
    norm_num at hp

/-- If `n` is prime and `n ≥ 7`, then `(n, n+1)` is not a Ruth–Aaron pair: indeed
`sopfr (n+1) < sopfr n`. -/
