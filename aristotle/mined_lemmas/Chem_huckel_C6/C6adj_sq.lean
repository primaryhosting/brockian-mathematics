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
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 2000000

namespace Chem

open Matrix

/-- The adjacency matrix (Hückel matrix, with `α = 0`, `β = 1`) of the cycle graph `C₆`,
i.e. of the benzene carbon skeleton. -/

theorem C6adj_sq :
    C6adj ^ 2 = !![2,0,1,0,1,0; 0,2,0,1,0,1; 1,0,2,0,1,0; 0,1,0,2,0,1; 1,0,1,0,2,0; 0,1,0,1,0,2] := by
  rw [pow_two, C6adj_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- The adjacency matrix `A` of `C₆` satisfies `A⁴ = 5A² - 4I`, i.e. it is annihilated by
`(X-2)(X-1)(X+1)(X+2)`. -/
