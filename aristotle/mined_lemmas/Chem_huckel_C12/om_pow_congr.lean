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

lemma om_pow_congr {a b : ℕ} (h : a ≡ b [MOD 12]) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 12]
  conv_rhs => rw [← Nat.div_add_mod b 12]
  simp only [pow_add, pow_mul, om_pow_twelve, one_pow, one_mul]
  exact congrArg _ h

