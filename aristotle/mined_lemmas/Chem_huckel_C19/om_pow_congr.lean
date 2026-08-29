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

theorem om_pow_congr {a b : ℕ} (h : a % 19 = b % 19) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 19]
  conv_rhs => rw [← Nat.div_add_mod b 19]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_19, one_pow, one_pow, h]

