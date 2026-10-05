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
# Counting Diverges Of Exists
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Set Topology

set_option maxHeartbeats 1000000

namespace Brockian.Weyl.WeylLawTarget

/-- The Weyl counting function of a set `S ⊆ ℝ` (thought of as a spectrum):
`countingFn S t` is the number of points of `S` that are `≤ t`. -/

noncomputable def countingFn (S : Set ℝ) (t : ℝ) : ℕ := (S ∩ Set.Iic t).ncard

/-- A spectrum is *locally finite* if only finitely many of its points lie below
any given threshold. -/
