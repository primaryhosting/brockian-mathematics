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

theorem gibbs_phase_rule_dof
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (C P : ℕ) (hP : 1 ≤ P)
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables C P)
    (hW : Module.finrank ℝ W = numConstraints C P) :
    Module.finrank ℝ (LinearMap.ker f) = degreesOfFreedom C P := by
  have h := gibbs_phase_rule C P hP f hf hV hW
  simp only [degreesOfFreedom]
  omega

/-- In particular the number of phases can never exceed `C + 2`: a system with more phases
than that cannot carry independent equilibrium constraints. -/
