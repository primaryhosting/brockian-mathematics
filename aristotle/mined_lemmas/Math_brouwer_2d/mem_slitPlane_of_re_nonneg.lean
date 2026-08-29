/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

open Complex Metric Set

/-- On a simply connected, locally path connected space, every continuous nowhere-vanishing
complex-valued function has a continuous logarithm.  This is the lifting property of the
covering map `exp : ℂ → ℂ \ {0}`. -/

theorem mem_slitPlane_of_re_nonneg {w : ℂ} (hre : 0 ≤ w.re) (hw : w ≠ 0) :
    w ∈ Complex.slitPlane := by
  rcases hre.lt_or_eq with h | h
  · exact Or.inl h
  · refine Or.inr fun him => hw ?_
    exact Complex.ext h.symm him

/-- Brouwer's fixed point theorem for the closed unit disk in `ℂ`. -/
