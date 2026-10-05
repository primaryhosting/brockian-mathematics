/-
# Twist Partial Sum Norm Le
Category: Characters
Target: Brockian.Characters5.twistPartialSum_norm_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian
namespace Characters5

/-- A primitive fifth root of unity. -/

lemma twistPartialSum_eq_mod (N : ℕ) : twistPartialSum N = twistPartialSum (N % 5) := by
  rw [twistPartialSum_eq_geom, twistPartialSum_eq_geom,
    geom_sum_eq omega_ne_one, geom_sum_eq omega_ne_one]
  congr 2
  conv_lhs => rw [← Nat.div_add_mod N 5]
  rw [pow_add, pow_mul, omega_pow_five, one_pow, one_mul]

/-- Bounded partial sums of the zero-mean twist: `‖∑_{n < N} e (n mod 5)‖ ≤ 2`. -/
