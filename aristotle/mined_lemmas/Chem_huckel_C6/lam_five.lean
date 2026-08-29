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

open SimpleGraph Matrix Real

namespace Chem

/-- The adjacency matrix of the cycle graph `C₆`, over `ℂ`
(the Hückel matrix of benzene in units where `α = 0`, `β = 1`). -/

lemma lam_five : lam 5 = 1 := by
  rw [lam, show (2 * π * ((5 : ℕ) : ℝ) / 6 : ℝ) = -(π / 3) + 2 * π by push_cast; ring,
    Real.cos_add_two_pi, Real.cos_neg, Real.cos_pi_div_three]
  norm_num

/-- A nonzero vector witnessing an eigenvalue, built from an explicit first-coordinate-nonzero
vector. -/
