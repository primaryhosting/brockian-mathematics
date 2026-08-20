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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

/-- The number of intensive state variables describing a heterogeneous system with `C`
components distributed over `P` phases: the temperature, the pressure, and, for every one of
the `P` phases, the `C` mole fractions of the components in that phase. -/

theorem gibbs_phase_rule_model (C P : ℕ) (hP : 1 ≤ P) (hPC : P ≤ C + 2) :
    Module.finrank ℝ
        (LinearMap.ker (LinearMap.fst ℝ (Fin (numConstraints C P) → ℝ)
          (Fin (C + 2 - P) → ℝ))) = degreesOfFreedom C P := by
  obtain ⟨-, -, hV, hW⟩ := gibbs_phase_rule_realizable C P hP hPC
  exact gibbs_phase_rule_dof C P hP _ LinearMap.fst_surjective hV hW

/-- A one-component system at a triple point (`C = 1`, `P = 3`) has no degrees of freedom:
the triple point is an isolated point of the phase diagram. -/
