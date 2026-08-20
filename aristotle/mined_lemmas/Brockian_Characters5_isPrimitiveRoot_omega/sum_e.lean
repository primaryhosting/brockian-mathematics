/-
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sum E Mul
Category: Characters
Target: Brockian.Characters5.sum_e_mul
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

namespace Brockian.Characters5

/-- A primitive fifth root of unity. -/

theorem sum_e : ∑ x : ZMod 5, e x = 0 := by
  have : ∑ x : ZMod 5, e x = ∑ k ∈ Finset.range 5, omega ^ k := by
    show (∑ x : Fin 5, omega ^ (x : ℕ)) = _
    simp [Fin.sum_univ_five, Finset.sum_range_succ]
  rw [this, sum_omega_pow]

