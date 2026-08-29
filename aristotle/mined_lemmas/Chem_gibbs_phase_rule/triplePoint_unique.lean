/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gibbs Phase Rule

Category: Chemistry.  Target: `Chem.gibbs_phase_rule`.

## Modelling

For a heterogeneous system with `C` chemical components distributed over `P` phases, the
*intensive* state of the system is a triple `(T, p, x)` consisting of

* the temperature `T` and the pressure `p` (2 variables), and
* the mole fractions `x j i` of component `i` in phase `j` (`P * C` variables),

so the state space `Chem.StateSpace C P = ℝ × ℝ × (Fin P → Fin C → ℝ)` has
`variableCount C P = 2 + P * C` dimensions.

The equilibrium conditions are

* the normalisation `∑ i, x j i = 1` of the mole fractions in each of the `P` phases, and
* the equality of the chemical potential of each of the `C` components between consecutive
  phases, which gives `C * (P - 1)` equations,

so the constraint space `Chem.ConstraintSpace C P = (Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)`
has `constraintCount C P = P + C * (P - 1)` dimensions.

Linearising the equilibrium conditions, they are described by a linear map
`L : StateSpace C P →ₗ[ℝ] ConstraintSpace C P`, and the (physical) assumption that the
conditions are *independent* is exactly the surjectivity of `L`.  The set of states realising
a prescribed value `c` of the constraints is then an affine subspace, namely a coset of
`ker L`, and its dimension is the number of degrees of freedom.  The theorem
`Chem.gibbs_phase_rule` computes that dimension to be `F = C - P + 2`.

`Chem.gibbs_phase_rule_coords` is the same statement written in flat coordinates
`Fin (variableCount C P) → ℝ` and `Fin (constraintCount C P) → ℝ`, and
`Chem.exists_surjective_constraintMap` shows the hypotheses are satisfiable (whenever
`1 ≤ P ≤ C + 2`), so the theorem is not vacuous.

`Chem.gibbs_phase_rule_nonlinear` upgrades the count to genuinely nonlinear equilibrium
conditions: near a regular equilibrium state, the implicit function theorem parametrises the
equilibrium set by `C - P + 2` real parameters.  Consequences of the count are
`Chem.phase_count_le` (`P ≤ C + 2`), `Chem.gibbs_invariant_point` (`P = C + 2` forces a unique
state) and `Chem.gibbs_infinite_of_phases_lt` (`P < C + 2` gives a continuum of states), and
`Chem.onePhaseRuleMap` and `Chem.triplePointMap` are explicit constraint maps realising the
classical cases `F = 1` (coexistence curve) and `F = 0` (triple point).
-/

namespace Chem

open Module Filter Topology

/-- Number of intensive variables: temperature, pressure and the `P * C` mole fractions. -/

theorem triplePoint_unique (c : ConstraintSpace 1 3) : ∃! v, triplePointMap v = c :=
  gibbs_invariant_point (by norm_num) (by norm_num) triplePointMap triplePointMap_surjective c

/-! ### Classical special cases -/

/-- One component, one phase: two degrees of freedom (`T` and `p` may vary freely). -/
example : degreesOfFreedom 1 1 = 2 := by decide

/-- One component, two coexisting phases: one degree of freedom (a coexistence curve). -/
example : degreesOfFreedom 1 2 = 1 := by decide

/-- One component, three coexisting phases: zero degrees of freedom (the triple point). -/
example : degreesOfFreedom 1 3 = 0 := by decide

/-- Two components, two phases: two degrees of freedom. -/
example : degreesOfFreedom 2 2 = 2 := by decide

end Chem

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

