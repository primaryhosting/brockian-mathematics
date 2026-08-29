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

namespace Chem

open Polynomial Matrix

/-- The Hückel (adjacency) matrix of the cycle graph `C₆` (the benzene ring), over `ℂ`. -/

lemma C6eig_eq_cos (k : Fin 6) :
    C6eig k = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 6) : ℝ) : ℂ) := by
  rw [two_cos_values k]
  fin_cases k <;> norm_num [C6eig]

/-- **Hückel theory for benzene (C₆).**
The characteristic polynomial of the adjacency (Hückel) matrix of the cycle graph `C₆`
factors as `∏ k, (X - 2·cos(2πk/6))`; that is, the adjacency eigenvalues of `C₆` are exactly
`2·cos(2πk/6)` for `k = 0, …, 5`, counted with multiplicity. -/
