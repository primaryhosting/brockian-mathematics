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

set_option grind.warning false

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when its residue class generates the
multiplicative group of `ZMod p`, i.e. when it has multiplicative order `p - 1`. -/

lemma neg_one_not_primitiveRoot (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have key : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd := orderOf_dvd_of_pow_eq_one key
  rw [IsPrimitiveRootMod] at h
  rw [h] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- A base case: `2` is a primitive root modulo `5`. -/
