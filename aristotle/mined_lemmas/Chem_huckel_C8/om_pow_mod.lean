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

set_option grind.warning false

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₈`. -/

lemma om_pow_mod (a b : ℕ) (h : a % 8 = b % 8) : om ^ a = om ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 8]
  conv_rhs => rw [← Nat.div_add_mod b 8]
  rw [pow_add, pow_add, pow_mul, pow_mul, om_pow_eight, one_pow, one_pow, h]

