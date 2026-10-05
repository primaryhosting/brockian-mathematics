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

def gibbsVariables (C P : ℕ) : ℕ := 2 + P * (C - 1)

/-- The number of independent equilibrium conditions: for each of the `C` components,
its chemical potential must agree across the `P` phases, giving `P - 1` independent
equations per component. -/
