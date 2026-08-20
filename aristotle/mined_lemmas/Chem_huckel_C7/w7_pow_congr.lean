/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix SimpleGraph

/-! ### A primitive 7th root of unity -/

/-- A primitive 7th root of unity. -/

lemma w7_pow_congr {a b : ℕ} (h : a % 7 = b % 7) : w7 ^ a = w7 ^ b := by
  conv_lhs => rw [← Nat.div_add_mod a 7, pow_add, pow_mul, w7_pow_seven, one_pow, one_mul, h]
  conv_rhs => rw [← Nat.div_add_mod b 7, pow_add, pow_mul, w7_pow_seven, one_pow, one_mul]

/-! ### The discrete Fourier (Vandermonde) matrix -/

/-- The discrete Fourier matrix of order 7, i.e. the Vandermonde matrix on the powers of `w7`. -/
