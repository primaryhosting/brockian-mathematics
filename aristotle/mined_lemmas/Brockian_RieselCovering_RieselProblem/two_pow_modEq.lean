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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- The Riesel number under consideration. -/

lemma two_pow_modEq (n : ℕ) : 2 ^ n ≡ 2 ^ (n % 24) [MOD M] := by
  have h24 : (2 : ℕ) ^ 24 ≡ 1 [MOD M] := by decide
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
  calc ((2 : ℕ) ^ 24) ^ (n / 24) * 2 ^ (n % 24)
      ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD M] := Nat.ModEq.mul (h24.pow _) rfl
    _ = 2 ^ (n % 24) := by ring

/-- The covering argument: for every `n`, one of the six primes of the covering set
`{3, 5, 7, 13, 17, 241}` divides `509203 * 2 ^ n - 1`. -/
