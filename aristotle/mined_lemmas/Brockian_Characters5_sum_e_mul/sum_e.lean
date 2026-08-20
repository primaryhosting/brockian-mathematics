/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
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

/-- The primitive fifth root of unity `exp (2 π i / 5)`. -/

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  have h : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => omega ^ k) 5]
    rfl
  rw [h, sum_omega_pow]

/-- Additive-character orthogonality on `ZMod 5`. -/
