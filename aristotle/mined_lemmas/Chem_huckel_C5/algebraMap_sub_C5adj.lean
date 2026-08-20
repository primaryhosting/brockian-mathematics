/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- The adjacency matrix of the cycle graph `C₅` (the Hückel matrix of cyclopentadienyl
in units where the Coulomb integral `α = 0` and the resonance integral `β = 1`). -/

lemma algebraMap_sub_C5adj (m : ℝ) :
    (algebraMap ℝ (Matrix (Fin 5) (Fin 5) ℝ) m - C5adj) =
      !![m, -1, 0, 0, -1;
        -1, m, -1, 0, 0;
         0, -1, m, -1, 0;
         0, 0, -1, m, -1;
        -1, 0, 0, -1, m] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj, Matrix.algebraMap_matrix_apply]

/-- The characteristic polynomial of the `C₅` adjacency matrix:
`det (μ I - A) = μ⁵ - 5μ³ + 5μ - 2`. -/
