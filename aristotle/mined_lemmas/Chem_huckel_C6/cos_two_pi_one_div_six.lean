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

lemma cos_two_pi_one_div_six : Real.cos (2 * Real.pi / 6) = 1 / 2 := by
  rw [show (2 * Real.pi / 6 : ℝ) = Real.pi / 3 by ring, Real.cos_pi_div_three]

