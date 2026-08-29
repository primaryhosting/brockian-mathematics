import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
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

open Matrix SimpleGraph

/-- A primitive 19-th root of unity. -/

theorem eig19_eq (k : Fin 19) : om ^ (18 * k.val) + om ^ k.val = eig19 k := by
  have h1 : om ^ (18 * k.val) * om ^ k.val = 1 := by
    rw [← pow_add, show 18 * k.val + k.val = 19 * k.val by ring, pow_mul, om_pow_19, one_pow]
  have hkey : om ^ (18 * k.val) = (om ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [hkey, om_pow_eq_exp k.val, ← Complex.exp_neg, eig19]
  push_cast
  rw [Complex.cos]
  ring_nf

