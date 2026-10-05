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

theorem perfectTotient_pow_three (k : ℕ) : PerfectTotient (3 ^ (k + 1)) := by
  refine ⟨Nat.pos_pow_of_pos _ (by norm_num), ?_⟩
  rw [totientIterSum_step (by
    have : (3:ℕ) ^ 1 ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this)]
  rw [totient_pow_three k, totientIterSum_two_mul_pow_three k]
  ring

/-- **Perfect Totient Infinitude**: there are infinitely many perfect totient numbers. -/
