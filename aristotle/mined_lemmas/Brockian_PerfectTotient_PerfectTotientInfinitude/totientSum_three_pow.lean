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

-- (Lean requires `import` to precede all other commands, so the required
-- header block appears immediately after the single import.)

namespace Brockian.PerfectTotient

/-- `totientSum n` is the sum of the iterated totients
`φ(n) + φ(φ(n)) + ⋯ + 1` of `n` (the iteration stopping when the value `1` is
reached, and that final `1` being included in the sum).  By convention
`totientSum 0 = totientSum 1 = 0`. -/

lemma totientSum_three_pow (k : ℕ) : totientSum (3 ^ (k + 1)) = 3 ^ (k + 1) := by
  have h2 : 2 ≤ 3 ^ (k + 1) := by
    calc 2 ≤ 3 ^ 1 := by norm_num
    _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hphi : Nat.totient (3 ^ (k + 1)) = 2 * 3 ^ k := by
    rw [Nat.totient_prime_pow (by norm_num) (Nat.succ_pos k)]
    simp [Nat.mul_comm]
  rw [totientSum_of_two_le h2, hphi, totientSum_two_mul_three_pow]
  ring

/-- Every power `3 ^ (k + 1)` is a perfect totient number. -/
