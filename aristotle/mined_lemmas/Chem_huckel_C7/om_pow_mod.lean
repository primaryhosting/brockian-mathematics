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

namespace Chem

open Polynomial Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₇` (the Hückel matrix of cycloheptatrienyl,
with `α = 0`, `β = 1`), as a real `7 × 7` matrix. -/

lemma om_pow_mod (n : ℕ) : om ^ (n % 7) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, om_pow_seven, one_pow, one_mul]

