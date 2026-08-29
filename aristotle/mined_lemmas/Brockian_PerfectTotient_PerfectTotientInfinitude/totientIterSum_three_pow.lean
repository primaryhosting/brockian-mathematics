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

Infinitely many perfect totient numbers: every power `3 ^ (k+1)` is one.
-/

namespace Brockian.PerfectTotient

/-- `totientIterSum n` is the sum of the iterated totients of `n`, i.e.
`φ(n) + φ(φ(n)) + φ(φ(φ(n))) + ⋯`, the iteration stopping once the value `1` is reached
(the terminal `1` is included in the sum, as is standard). -/

lemma totientIterSum_three_pow (k : ℕ) : totientIterSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    have : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
    calc 2 ≤ 3 * 1 := by norm_num
      _ ≤ 3 * 3 ^ k := Nat.mul_le_mul_left 3 this
      _ = 3 ^ (k + 1) := by ring
  rw [totientIterSum_eq _ h2, totient_three_pow k, totientIterSum_two_mul_three_pow k]
  ring

