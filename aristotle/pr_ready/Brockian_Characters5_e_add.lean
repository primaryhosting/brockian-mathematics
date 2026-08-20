/-!
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
Statement: e is an additive-to-multiplicative homomorphism: e (j + k) = e j * e k for all j k : ZMod 5.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity in `ℂ`. -/
noncomputable def omega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The additive character `e : ZMod 5 → ℂ`, `e j = ω ^ j.val`. -/
noncomputable def e (j : ZMod 5) : ℂ := omega ^ j.val

theorem omega_pow_five : omega ^ 5 = 1 := by
  have h : omega ^ (5 : ℕ) = Complex.exp (2 * Real.pi * Complex.I) := by
    rw [omega, ← Complex.exp_nat_mul]
    ring_nf
  rw [h]
  simp [Complex.exp_two_pi_mul_I]

theorem e_add (j k : ZMod 5) : e (j + k) = e j * e k := by
  rw [e, e, e, ← pow_add]
  have hval : (j + k).val = (j.val + k.val) % 5 := by
    rw [ZMod.val_add]
  rw [hval]
  conv_rhs => rw [← Nat.div_add_mod (j.val + k.val) 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

end Characters5
end Brockian

