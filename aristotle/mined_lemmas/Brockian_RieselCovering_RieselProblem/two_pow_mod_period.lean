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

namespace Brockian.RieselCovering

/-- The Riesel number under consideration: `509203`. -/

lemma two_pow_mod_period {p : ℕ} (hp : 2 ^ 24 % p = 1) (n : ℕ) :
    2 ^ n % p = 2 ^ (n % 24) % p := by
  conv_lhs => rw [← Nat.div_add_mod n 24, pow_add, pow_mul]
  rw [Nat.mul_mod, Nat.pow_mod, hp, one_pow, ← Nat.mul_mod, one_mul]

/-- The covering property at each residue: `k * 2 ^ r ≡ 1` modulo the assigned prime. -/
