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
# Perfect Totient Infinitude
Category: Brockian Conjecture
Target: Brockian.PerfectTotient.PerfectTotientInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PerfectTotient

open Nat

/-- `totientSum n` is the sum of the iterated totients
`φ n + φ (φ n) + φ (φ (φ n)) + ⋯`, continued until the value `1` is reached
(the final `1` being included in the sum).  By convention it is `0` for `n ≤ 1`. -/

theorem totientSum_two_mul_pow_three (j : ℕ) : totientSum (2 * 3 ^ j) = 3 ^ j := by
  induction j with
  | zero =>
      show totientSum 2 = 1
      rw [totientSum_succ_succ 0]
      norm_num [Nat.totient_two, totientSum]
  | succ j ih =>
      have h2 : 2 ≤ 2 * 3 ^ (j + 1) := by
        have : 1 ≤ 3 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega
      rw [totientSum_eq _ h2, totient_two_mul_pow_three, ih]
      ring

/-- Every power `3 ^ (k+1)` is a perfect totient number. -/
