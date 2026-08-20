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

lemma charpoly_complex :
    ((cycleGraph 7).adjMatrix ℂ).charpoly = ∏ k : Fin 7, (X - C (lam7 k)) := by
  have hdet : IsUnit dft7.det := isUnit_iff_ne_zero.mpr dft7_det_ne_zero
  have key : ((cycleGraph 7).adjMatrix ℂ)
      = (Matrix.nonsingInvUnit dft7 hdet).val * (Matrix.diagonal lam7)
        * (Matrix.nonsingInvUnit dft7 hdet)⁻¹.val := by
    show _ = dft7 * Matrix.diagonal lam7 * dft7⁻¹
    rw [← adj_mul_dft7, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  rw [key, Matrix.charpoly_units_conj, Matrix.charpoly_diagonal]

