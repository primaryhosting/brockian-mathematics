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

theorem huckel_prod_eq : (∏ k : Fin 4, (X - C (huckelEigenvalue k))) = (X : ℝ[X]) ^ 4 - 4 * X ^ 2 := by
  simp only [huckelEigenvalue_eq, Fin.prod_univ_four]
  norm_num [C_ofNat, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
  ring

/-- The Hückel eigenvector components are powers of `i`. -/
