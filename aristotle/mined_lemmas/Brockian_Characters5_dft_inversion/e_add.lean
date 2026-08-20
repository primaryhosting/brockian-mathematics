import Mathlib

/-!
# Dft Inversion
Category: Characters
Target: Brockian.Characters5.dft_inversion
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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/
noncomputable def ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)


lemma e_add (a b : ZMod 5) : e (a + b) = e a * e b := by
  have hval : (a + b).val = (a.val + b.val) % 5 := ZMod.val_add a b
  have h : ω ^ (a.val + b.val) = ω ^ ((a.val + b.val) % 5) := by
    conv_lhs => rw [← Nat.div_add_mod (a.val + b.val) 5]
    rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]
  simp only [e, hval, ← pow_add, h]

