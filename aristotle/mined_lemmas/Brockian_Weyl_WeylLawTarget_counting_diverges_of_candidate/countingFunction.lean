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
# Counting Diverges Of Candidate
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_candidate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open Filter Set
open scoped Topology

namespace Brockian.Weyl.WeylLawTarget

/-- A *candidate spectrum* is a nondecreasing sequence of real numbers tending to `+∞`.
This is the abstract shape of the eigenvalue sequence appearing in a Weyl law:
eigenvalues listed in nondecreasing order and accumulating only at infinity. -/
structure IsCandidateSpectrum (mu : ℕ → ℝ) : Prop where
  mono : Monotone mu
  tendsto : Filter.Tendsto mu Filter.atTop Filter.atTop

/-- The eigenvalue counting function of a candidate spectrum:
`countingFunction mu L` is the number of indices `n` with `mu n ≤ L`. -/

noncomputable def countingFunction (mu : ℕ → ℝ) (L : ℝ) : ℕ := {n : ℕ | mu n ≤ L}.ncard

/-- For a sequence tending to `+∞`, only finitely many terms lie below any given level. -/
