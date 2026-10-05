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

import Mathlib

/-!
# Huckel C 6
Category: Chemistry
Target: Chem.huckel_C6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆` (the Hückel matrix of benzene with
`α = 0`, `β = 1`), written out explicitly. -/

lemma C6adj_poly : C6adj ^ 4 - (5 : ℂ) • C6adj ^ 2 + (4 : ℂ) • 1 = 0 := by
  have h4 : C6adj ^ 4 = (C6adj ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, C6adj_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pow_two] <;> norm_num

/-- Any eigenvalue of the adjacency matrix of `C₆` lies in `{2, 1, -1, -2}`. -/
