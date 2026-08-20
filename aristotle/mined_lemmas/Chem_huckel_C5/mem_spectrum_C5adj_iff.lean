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

lemma mem_spectrum_C5adj_iff (m : ℝ) :
    m ∈ spectrum ℝ C5adj ↔ m ^ 5 - 5 * m ^ 3 + 5 * m - 2 = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, det_algebraMap_sub_C5adj,
    isUnit_iff_ne_zero, not_ne_iff]

