import Mathlib

/-!
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
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

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity in `ℂ`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e j = ω ^ j.val`. -/
noncomputable def e (j : ZMod 5) : ℂ := omega ^ j.val

/-- `ω ^ 5 = 1`. -/
theorem omega_pow_five : omega ^ 5 = 1 := by
  have h : omega ^ (5 : ℕ) = Complex.exp (2 * Real.pi * Complex.I) := by
    rw [omega, ← Complex.exp_nat_mul]
    congr 1
    ring
  rw [h]
  simp

/-- Key intermediate lemma: `ω ^ n` only depends on `n % 5`. -/
theorem omega_pow_mod (n : ℕ) : omega ^ (n % 5) = omega ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

/-- `e` is an additive-to-multiplicative homomorphism. -/
theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  rw [e, e, e, ← pow_add, ZMod.val_add, omega_pow_mod]

end Characters5
end Brockian

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

