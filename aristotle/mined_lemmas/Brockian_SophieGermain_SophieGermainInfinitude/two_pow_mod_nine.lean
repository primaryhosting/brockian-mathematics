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
# Sophie Germain Infinitude
Category: Brockian Conjecture
Target: Brockian.SophieGermain.SophieGermainInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.SophieGermain

/-- `p` is a Sophie Germain prime if both `p` and `2 * p + 1` are prime. -/

lemma two_pow_mod_nine (n : ℕ) : 2 ^ n % 9 = 2 ^ (n % 6) % 9 := by
  conv_lhs => rw [← Nat.div_add_mod n 6]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

end Auxiliary

/-- **Criterion, minus case.** If `p` is prime and `2 * p + 1` divides `2 ^ p - 1`,
then `2 * p + 1` is prime. -/
