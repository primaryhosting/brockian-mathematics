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

lemma sopfr_lt_of_even {n : ℕ} (hn : 8 ≤ n) (h2 : 2 ∣ n) : sopfr n < n - 1 := by
  obtain ⟨m, rfl⟩ := h2
  have h : sopfr (2 * m) = 2 + sopfr m := by
    rw [sopfr_mul (by norm_num) (by omega), sopfr_prime (by norm_num)]
  have hle := sopfr_le_self m
  omega

/-- `sopfr` of a product of a list of primes is the sum of that list. -/
