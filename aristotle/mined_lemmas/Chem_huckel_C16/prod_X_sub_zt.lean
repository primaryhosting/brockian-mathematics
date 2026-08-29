/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
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
set_option maxRecDepth 10000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ### The shift matrices

`U n` is the matrix of the `n`-fold cyclic shift on `Fin 16`; the adjacency matrix of the
cycle graph `C₁₆` is `U 1 + U 15`. -/

/-- The matrix of the `n`-fold cyclic shift of `Fin 16`. -/

theorem prod_X_sub_zt : ∏ i ∈ Finset.range 16, (X - C (zt ^ i)) = X ^ 16 - 1 := by
  have h := X_pow_sub_C_eq_prod zt_prim (by norm_num) (one_pow 16)
  simp only [mul_one, map_one] at h
  rw [← h]

/-- The `k`-th Hückel eigenvalue `2·cos(2πk/16)`, viewed as a complex number. -/
