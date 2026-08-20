/-
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
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

namespace Chem

open Polynomial Matrix Complex

/-- A primitive 10-th root of unity. -/

lemma det_U10_ne_zero : (U10).det ≠ 0 := by
  have hprim : IsPrimitiveRoot w 10 := by
    have := Complex.isPrimitiveRoot_exp 10 (by norm_num)
    simpa [w] using this
  refine Matrix.det_vandermonde_ne_zero_iff.mpr ?_
  intro i j hij
  exact Fin.ext (hprim.pow_inj i.isLt j.isLt hij)

