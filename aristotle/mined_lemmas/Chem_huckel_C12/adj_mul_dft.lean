import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators Real
open Polynomial Matrix

namespace Chem

/-- A primitive 12-th root of unity. -/

lemma adj_mul_dft : adjC12 * dftC12 = dftC12 * Matrix.diagonal eigC12 := by
  ext i k
  have hne : i + 1 ≠ i - 1 := by revert i; decide
  have hsucc : (i + 1).val = (i.val + 1) % 12 := by simp [Fin.val_add]
  have hpred : (i - 1).val = (i.val + 11) % 12 := by revert i; decide
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  rw [show (∑ j, adjC12 i j * dftC12 j k)
      = ∑ j, (if j = i + 1 ∨ j = i - 1 then (1 : ℂ) else 0) * dftC12 j k from rfl,
    sum_two_ite _ _ hne]
  have e1 : dftC12 (i + 1) k = om ^ (i.val * k.val + k.val) := by
    rw [dftC12, hsucc]
    refine om_pow_congr ?_
    have h1 : ((i.val + 1) % 12) * k.val ≡ (i.val + 1) * k.val [MOD 12] :=
      (Nat.mod_modEq (i.val + 1) 12).mul_right k.val
    have h2 : (i.val + 1) * k.val = i.val * k.val + k.val := by ring
    rw [h2] at h1
    exact h1
  have e2 : dftC12 (i - 1) k = om ^ (i.val * k.val + (12 - k.val)) := by
    rw [dftC12, hpred]
    refine om_pow_congr ?_
    have h1 : ((i.val + 11) % 12) * k.val ≡ (i.val + 11) * k.val [MOD 12] :=
      (Nat.mod_modEq (i.val + 11) 12).mul_right k.val
    have h2 : (i.val + 11) * k.val = i.val * k.val + 11 * k.val := by ring
    have h3 : i.val * k.val + 11 * k.val ≡ i.val * k.val + (12 - k.val) [MOD 12] := by
      unfold Nat.ModEq; omega
    exact h1.trans (h2 ▸ h3)
  rw [e1, e2, dftC12, ← om_add_inv k, pow_add, pow_add]
  ring

