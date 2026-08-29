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

lemma totient_three_pow (k : ℕ) : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
  rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
  simp [Nat.mul_comm]

