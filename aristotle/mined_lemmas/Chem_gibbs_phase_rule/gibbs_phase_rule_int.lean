/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
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

set_option grind.warning false

namespace Chem

/-- The number of intensive state variables describing a heterogeneous system with
`C` chemical components distributed over `P` phases: temperature and pressure, plus,
for each phase, the `C - 1` independent mole fractions of that phase (the last one is
fixed by the requirement that the mole fractions of a phase sum to `1`). -/

theorem gibbs_phase_rule_int (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P)
    (f : (Fin (gibbsVariables C P) → ℝ) →ₗ[ℝ] (Fin (gibbsConstraints C P) → ℝ))
    (hf : Function.Surjective f) :
    (Module.finrank ℝ (LinearMap.ker f) : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  have h := gibbs_phase_rule C P hC hP f hf
  omega

/-- The hypotheses of `gibbs_phase_rule` are not vacuous: whenever `1 ≤ C`, `1 ≤ P`
and `P ≤ C + 2` (the physically meaningful range, in which the number of equilibrium
conditions does not exceed the number of variables), an independent system of
equilibrium conditions — i.e. a surjective linear map — does exist. -/
