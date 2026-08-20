/-
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 3
Category: Chemistry
Target: Chem.huckel_C3
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

/-- The Hückel (adjacency) matrix of the cycle graph `C₃`: the π-system connectivity
matrix of a three-membered carbon ring, in units where the Coulomb integral is `α = 0`
and the resonance integral is `β = 1`. -/

lemma huckel_val_two : 2 * Real.cos (2 * Real.pi * (2 : ℕ) / 3) = -1 := by
  have h : 2 * Real.pi * ((2 : ℕ) : ℝ) / 3 = Real.pi + Real.pi / 3 := by
    push_cast; ring
  rw [h, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_three]
  norm_num

/-- The characteristic polynomial of the `C₃` adjacency matrix is `X³ - 3X - 2`. -/
