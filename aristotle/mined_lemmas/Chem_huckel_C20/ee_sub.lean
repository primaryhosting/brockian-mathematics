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

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

lemma ee_sub (x y : Fin 20) : ee (x - y) = ee x * (ee y)⁻¹ := by
  have h : ee (x - y) * ee y = ee x := by rw [← ee_add, sub_add_cancel]
  exact (eq_mul_inv_iff_mul_eq₀ (ee_ne_zero y)).mpr h

