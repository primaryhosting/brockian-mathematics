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

lemma adj_mul_dft7 :
    ((cycleGraph 7).adjMatrix ℂ) * dft7 = dft7 * Matrix.diagonal lam7 := by
  ext i k
  rw [Matrix.mul_apply, adj_mul_row i (fun j => dft7 j k), Matrix.mul_diagonal,
    cyc7_sub_one, dft7_shift, dft7_shift, dft7_apply, lam7]
  norm_num [pow_add, mul_add]
  ring

