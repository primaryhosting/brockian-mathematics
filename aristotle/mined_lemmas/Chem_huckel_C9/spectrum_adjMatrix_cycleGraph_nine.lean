/-
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
open Complex Polynomial SimpleGraph

namespace Chem

/-- A primitive `9`-th root of unity. -/

theorem spectrum_adjMatrix_cycleGraph_nine :
    spectrum ℂ ((cycleGraph 9).adjMatrix ℂ) =
      {mu : ℂ | ∃ k : ℕ, k < 9 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 9) : ℝ) : ℂ)} := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, IsRoot, huckel_C9]
  simp only [eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_range,
    sub_eq_zero, Set.mem_setOf_eq]

end Chem

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

