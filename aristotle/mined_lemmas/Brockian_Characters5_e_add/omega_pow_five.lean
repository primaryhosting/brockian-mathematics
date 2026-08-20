/-
# E Add
Category: Characters
Target: Brockian.Characters5.e_add
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity in `ℂ`. -/

theorem omega_pow_five : omega ^ 5 = 1 := by
  have h : omega ^ (5 : ℕ) = Complex.exp (2 * Real.pi * Complex.I) := by
    rw [omega, ← Complex.exp_nat_mul]
    ring_nf
  rw [h]
  simp [Complex.exp_two_pi_mul_I]

