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
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wilson Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.WilsonPrimes.WilsonPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat

namespace Brockian.WilsonPrimes

/-- A *Wilson prime* is a prime `p` such that `p ^ 2` divides `(p - 1)! + 1`.
(By Wilson's theorem, `p` itself always divides `(p - 1)! + 1` when `p` is prime,
so a Wilson prime is one for which this divisibility holds to the second power.) -/

lemma dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) : p ∣ (p - 1)! + 1 := by
  have h1 : ((p - 1)! : ZMod p) = -1 :=
    (Nat.prime_iff_fac_equiv_neg_one hp.ne_one).1 hp
  have h2 : (((p - 1)! + 1 : ℕ) : ZMod p) = 0 := by
    push_cast [h1]; ring
  exact (ZMod.natCast_eq_zero_iff _ _).1 h2

/-- The *Wilson quotient* of `p`, namely `((p - 1)! + 1) / p`.
For prime `p` this is an integer by Wilson's theorem. -/
