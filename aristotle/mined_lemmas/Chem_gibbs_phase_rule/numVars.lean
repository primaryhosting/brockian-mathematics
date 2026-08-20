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

/-!
# The Gibbs phase rule as an affine dimension count

For a system with `C` chemical components distributed over `P` phases in equilibrium,
the intensive state is described by

* the temperature `T` and the pressure `p` (2 variables), together with
* the mole fractions `x (i, j)` of component `i` in phase `j` (`P * C` variables),

so the ambient space has dimension `numVars C P = 2 + P * C`.

These variables are subject to

* one normalisation `∑ i, x (i, j) = 1` per phase (`P` equations), and
* the equality of the chemical potential of each component across all phases,
  `μ i 1 = μ i 2 = … = μ i P` (`C * (P - 1)` equations),

so there are `numConstraints C P = P + C * (P - 1)` equations.

Assuming the constraints are independent — formalised as the surjectivity of the
(linearised) constraint map `L` — the set of equilibrium states is an affine subspace of
dimension

`numVars C P - numConstraints C P = C - P + 2`,

which is the number `F` of degrees of freedom.  This is the content of
`Chem.gibbs_phase_rule` (kernel form) and `Chem.gibbs_phase_rule_affine` (affine form).
-/

namespace Chem

/-- The number of intensive variables of a `C`-component, `P`-phase system:
temperature, pressure, and the mole fraction of each component in each phase. -/

def numVars (C P : ℕ) : ℕ := 2 + P * C

/-- The number of equilibrium constraints of a `C`-component, `P`-phase system:
one mole-fraction normalisation per phase, and the equality of the chemical potential
of each component across the `P` phases. -/
