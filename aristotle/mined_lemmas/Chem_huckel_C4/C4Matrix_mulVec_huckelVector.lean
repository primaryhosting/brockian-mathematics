/-
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 4
Category: Chemistry
Target: Chem.huckel_C4
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial

/-- The Hückel (adjacency) matrix of the carbon skeleton of cyclobutadiene `C₄`,
i.e. the adjacency matrix of the cycle graph `C₄`, with coefficients in `R`. -/

theorem C4Matrix_mulVec_huckelVector (k : Fin 4) :
    (C4Matrix ℂ).mulVec (huckelVector k) = ((huckelEigenvalue k : ℝ) : ℂ) • huckelVector k := by
  funext i
  rw [C4Matrix_eq]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_four, huckelVector_eq, huckelEigenvalue_eq,
    Pi.smul_apply, smul_eq_mul]
  fin_cases k <;> fin_cases i <;>
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, pow_succ,
      Complex.I_sq]

/-- **Hückel theory for cyclobutadiene (C₄).**
The adjacency eigenvalues of the cycle graph `C₄` are exactly `2 cos (2πk/4)` for `k = 0,1,2,3`:

* the characteristic polynomial of the adjacency matrix factors as
  `∏ k, (X - 2 cos (2πk/4))`, so these are the eigenvalues with multiplicity;
* each Fourier mode `j ↦ exp (2πi k j / 4)` is a nonzero eigenvector with eigenvalue
  `2 cos (2πk/4)`. -/
