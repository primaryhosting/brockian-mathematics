import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
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

open Polynomial Matrix SimpleGraph

/-- A primitive 17-th root of unity. -/

lemma lam_eq (k : Fin 17) : ((lam k : ℝ) : ℂ) = zeta ^ k.val + zeta ^ (16 * k.val) := by
  have h16 : zeta ^ (16 * k.val) = (zeta ^ k.val)⁻¹ := by
    have hz : zeta ^ k.val ≠ 0 := pow_ne_zero _ zeta_ne_zero
    have : zeta ^ (16 * k.val) * zeta ^ k.val = 1 := by
      rw [← pow_add]
      have : 16 * k.val + k.val = 17 * k.val := by ring
      rw [this, pow_mul, zeta_pow_17, one_pow]
    field_simp at this ⊢
    linear_combination this
  rw [h16, zeta_pow_eq_exp, ← Complex.exp_neg]
  rw [lam]
  push_cast
  rw [Complex.two_cos]
  congr 2
  ring

