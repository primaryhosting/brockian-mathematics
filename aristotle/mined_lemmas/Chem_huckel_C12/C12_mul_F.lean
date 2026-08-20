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

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma C12_mul_F : C12 * F = F * Matrix.diagonal lam := by
  ext i k
  rw [Matrix.mul_apply, C12_row_sum i (fun j => F j k), Matrix.mul_diagonal]
  have h1 : (i - 1) * k = i * k + -k := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  simp only [F, Matrix.of_apply, h1, h2, ee_add]
  rw [← mul_add, add_comm (ee (-k)) (ee k), ee_add_neg]

