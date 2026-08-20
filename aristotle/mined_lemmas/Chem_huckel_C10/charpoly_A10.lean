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

lemma charpoly_A10 :
    A10.charpoly = ∏ k : Fin 10, (X - C ((huckelEigenvalue k : ℂ))) := by
  have hU : IsUnit U10.det := isUnit_iff_ne_zero.mpr det_U10_ne_zero
  have key : A10 = (U10.nonsingInvUnit hU).val * D10 * ((U10.nonsingInvUnit hU)⁻¹).val := by
    show A10 = U10 * D10 * U10⁻¹
    rw [← A10_mul_U10, mul_assoc, Matrix.mul_nonsing_inv _ hU, mul_one]
  rw [key, Matrix.charpoly_units_conj, D10, Matrix.charpoly_diagonal]

/-- **Hückel theory for C₁₀.**  The characteristic polynomial of the adjacency matrix of the
cycle graph `C₁₀` factors as `∏ k, (X - 2 cos (2πk/10))`; consequently the eigenvalues
(spectrum) of that matrix are exactly the numbers `2 cos (2πk/10)`, `k = 0, …, 9`. -/
