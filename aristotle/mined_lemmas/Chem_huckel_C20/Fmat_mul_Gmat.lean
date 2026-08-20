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

lemma Fmat_mul_Gmat : Fmat * Gmat = 1 := by
  ext j k
  rw [Matrix.mul_apply]
  have hterm : ∀ m : Fin 20, Fmat j m * Gmat m k = (20 : ℂ)⁻¹ * ec (m * (j - k)) := by
    intro m
    simp only [Fmat, Gmat, Matrix.of_apply]
    rw [mul_sub, sub_eq_add_neg, ec_add, ec_neg, mul_comm m j]
    ring
  rw [Finset.sum_congr rfl fun m _ => hterm m, ← Finset.mul_sum, sum_ec_pow]
  by_cases h : j = k
  · subst h
    simp
  · rw [if_neg (by simpa [sub_eq_zero] using h)]
    rw [Matrix.one_apply_ne h]
    ring

