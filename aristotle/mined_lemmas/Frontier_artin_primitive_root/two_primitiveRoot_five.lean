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

lemma two_primitiveRoot_five : IsPrimitiveRootMod 2 5 := by
  have h4 : ((2 : ℤ) : ZMod 5) ^ 4 = 1 := by decide
  have hd := orderOf_dvd_of_pow_eq_one h4
  have h2 : ¬ (orderOf ((2 : ℤ) : ZMod 5) ∣ 2) := by
    intro hh
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hh) (by decide)
  have hle : orderOf ((2 : ℤ) : ZMod 5) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  rw [IsPrimitiveRootMod]
  generalize orderOf ((2 : ℤ) : ZMod 5) = n at *
  interval_cases n <;> simp_all

/-- Primitive roots exist modulo every prime: the unit group of `ZMod p` is cyclic. -/
