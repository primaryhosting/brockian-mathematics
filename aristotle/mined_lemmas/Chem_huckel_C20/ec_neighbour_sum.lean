/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
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

namespace Chem

open Polynomial Matrix

/-! ### The 20-th root of unity and the characters of `Fin 20` -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma ec_neighbour_sum (j k : Fin 20) :
    ec ((j - 1) * k) + ec ((j + 1) * k)
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 20) : ℝ) : ℂ) * ec (j * k) := by
  rw [← ec_add_inv k,
    show (j - 1) * k = j * k + (-k) by rw [sub_mul, one_mul, sub_eq_add_neg],
    show (j + 1) * k = j * k + k by rw [add_mul, one_mul],
    ec_add, ec_add, ec_neg]
  ring

