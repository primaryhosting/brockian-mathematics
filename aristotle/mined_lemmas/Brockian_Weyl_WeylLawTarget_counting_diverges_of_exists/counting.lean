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

namespace Brockian.Weyl.WeylLawTarget

open Filter Set

/-- The Weyl counting function of a spectrum `S ⊆ ℝ`: the number of spectral points
that are `≤ lam`. -/

noncomputable def counting (S : Set ℝ) (lam : ℝ) : ℕ := (S ∩ Set.Iic lam).ncard

/-- A discrete spectrum with infinitely many points has a divergent counting function:
`counting S lam → ∞` as `lam → ∞`.

The hypothesis `hdisc` says the spectrum is locally finite from below (each spectral
window `(-∞, lam]` contains only finitely many points), and `hex` says there are
infinitely many spectral points. -/
