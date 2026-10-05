import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. when the multiplicative order of `a` in `ZMod p`
equals `p - 1`. -/

theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI := Fact.mk hp
  intro h
  have hsq : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [h] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- For `a = -1` the set of primes with `-1` a primitive root is contained in `{2, 3}`. -/
