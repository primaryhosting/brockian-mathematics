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

lemma om_add_inv (k : Fin 12) : om ^ k.val + om ^ (12 - k.val) = eigC12 k := by
  have hk : k.val ≤ 12 := k.isLt.le
  rw [om_pow_eq_exp, om_pow_eq_exp, Complex.exp_mul_I, Complex.exp_mul_I, eigC12]
  have h1 : ((12 - k.val : ℕ) : ℝ) = 12 - (k.val : ℝ) := by
    push_cast [Nat.cast_sub hk]; ring
  rw [h1]
  have h2 : (2 * Real.pi * (12 - (k.val : ℝ)) / 12)
      = 2 * Real.pi - (2 * Real.pi * k.val / 12) := by ring
  rw [h2]
  push_cast
  rw [Complex.cos_sub, Complex.sin_sub]
  simp [Complex.cos_two_pi, Complex.sin_two_pi]
  ring

