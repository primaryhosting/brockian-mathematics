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

A *perfect totient number* is a positive integer `n` equal to the sum of its iterated
totients `φ n + φ (φ n) + ⋯ + 1`.  We show that the set of such numbers is infinite,
by proving that every power `3 ^ (k+1)` is a perfect totient number.
-/

namespace Brockian.PerfectTotient

/-- `totientSum n` is the sum of the iterated totients of `n`:
`φ n + φ (φ n) + ⋯ + 1`, the iteration stopping once the value reaches `1`. -/

lemma totient_two_mul_three_pow (k : ℕ) :
    Nat.totient (2 * 3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_mul (Nat.Coprime.pow_right _ (show Nat.Coprime 2 3 by decide)),
    Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
  simp only [Nat.totient_two, one_mul, Nat.succ_sub_one]
  ring

/-- The iterated totient sum of `2 * 3 ^ k` is `3 ^ k`. -/
