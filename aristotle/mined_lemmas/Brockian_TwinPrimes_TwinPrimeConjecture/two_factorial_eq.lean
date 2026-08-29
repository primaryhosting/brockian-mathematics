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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.TwinPrimes

open Nat

/-- `p` is a twin prime (the smaller member of a twin prime pair) if both `p` and `p + 2`
are prime. -/

private lemma two_factorial_eq (k : ℕ) (hq : Nat.Prime (k + 5)) :
    (2 : ZMod (k + 5)) * ((k + 2)! : ℕ) = -1 := by
  have hw := (Nat.prime_iff_fac_equiv_neg_one (n := k + 5) (by omega)).mp hq
  rw [show (k + 5) - 1 = k + 4 from rfl] at hw
  rw [factorial_step k] at hw
  have h0 : ((k : ZMod (k + 5)) + 5) = 0 := by
    have : ((k + 5 : ℕ) : ZMod (k + 5)) = 0 := ZMod.natCast_self _
    push_cast at this
    linear_combination this
  have hk4 : ((k : ZMod (k + 5)) + 4) = -1 := by linear_combination h0
  have hk3 : ((k : ZMod (k + 5)) + 3) = -2 := by linear_combination h0
  push_cast at hw
  rw [hk4, hk3] at hw
  linear_combination hw

/-- **Clement's criterion** (forward direction): if `n` and `n + 2` are both prime and `n ≥ 3`,
then `n * (n + 2) ∣ 4 * ((n - 1)! + 1) + n`. -/
