/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial Matrix Complex SimpleGraph Finset

namespace Chem

/-- The primitive 19-th root of unity `exp (2πi/19)`. -/

theorem huckel_C19_spectrum :
    spectrum ℂ C19adj =
      {mu : ℂ | ∃ k : ℕ, k < 19 ∧ mu = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)} := by
  ext mu
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, huckel_C19]
  simp only [Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero, Finset.mem_range,
    Set.mem_setOf_eq]

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

