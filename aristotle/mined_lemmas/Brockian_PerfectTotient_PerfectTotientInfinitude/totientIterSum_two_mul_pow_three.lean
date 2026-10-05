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
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PerfectTotient

/-- `totientIterSum n` is the sum of the iterated totients of `n`:
`φ(n) + φ(φ(n)) + ⋯ + 1`, the iteration stopping once the value `1` is reached.
By convention the sum is `0` for `n ≤ 1`. -/

lemma totientIterSum_two_mul_pow_three (k : ℕ) :
    totientIterSum (2 * 3 ^ k) = 3 ^ k := by
  induction k with
  | zero => simp [totientIterSum]
  | succ k ih =>
      rw [totientIterSum_step (by
        have : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega)]
      rw [totient_two_mul_pow_three k, ih]
      ring

/-- Every power `3 ^ (k+1)` is a perfect totient number. -/
