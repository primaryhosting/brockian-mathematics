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

/-- `a : ℤ` is a *primitive root* modulo `p` when the image of `a` in `ZMod p` has
multiplicative order exactly `p - 1`, i.e. it generates the group of units of `ZMod p`. -/

theorem eq_two_or_three_of_isPrimitiveRootMod_neg_one {p : ℕ} (hp : Nat.Prime p)
    (h : IsPrimitiveRootMod (-1) p) : p = 2 ∨ p = 3 := by
  unfold IsPrimitiveRootMod at h
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hp2 : 2 ≤ p := hp.two_le
  have hcast : ((-1 : ℤ) : ZMod p) = -1 := by push_cast; ring
  rw [hcast] at h
  have : orderOf (-1 : ZMod p) ≤ 2 := by
    apply Nat.le_of_dvd (by norm_num)
    apply orderOf_dvd_of_pow_eq_one
    simp
  omega

