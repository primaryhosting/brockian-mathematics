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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is never prime
for `n ≥ 1`. -/

lemma two_pow_modEq_two_pow_mod (p n : ℕ) (hp : 2 ^ 24 ≡ 1 [MOD p]) :
    2 ^ n ≡ 2 ^ (n % 24) [MOD p] := by
  conv_lhs => rw [← Nat.div_add_mod n 24]
  calc 2 ^ (24 * (n / 24) + n % 24)
      = (2 ^ 24) ^ (n / 24) * 2 ^ (n % 24) := by rw [pow_add, pow_mul]
    _ ≡ 1 ^ (n / 24) * 2 ^ (n % 24) [MOD p] := Nat.ModEq.mul (hp.pow _) (Nat.ModEq.refl _)
    _ = 2 ^ (n % 24) := by rw [one_pow, one_mul]

/-- Transfer of a divisibility `p ∣ 509203 * 2 ^ r - 1` from the residue `r = n % 24`
to the exponent `n` itself, given that `2` has order dividing `24` modulo `p`. -/
