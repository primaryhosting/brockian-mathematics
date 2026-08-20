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

theorem one_component_triple_point
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W]
    (f : V →ₗ[ℝ] W) (hf : Function.Surjective f)
    (hV : Module.finrank ℝ V = numVariables 1 3)
    (hW : Module.finrank ℝ W = numConstraints 1 3) :
    Module.finrank ℝ (LinearMap.ker f) = 0 := by
  have h := gibbs_phase_rule 1 3 (by norm_num) f hf hV hW
  omega

/-- A one-component, two-phase system (`C = 1`, `P = 2`) has one degree of freedom: its
coexistence states form a curve, e.g. the vapour-pressure curve. -/
