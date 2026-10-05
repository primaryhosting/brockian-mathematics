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

def gibbsConstraints (C P : ℕ) : ℕ := C * (P - 1)

/-- **Gibbs' phase rule**, as an affine-dimension count.

The intensive state of a system of `C` components in `P` phases is described by
`gibbsVariables C P = 2 + P * (C - 1)` real variables, subject to the
`gibbsConstraints C P = C * (P - 1)` equilibrium conditions expressed by a linear map
`f`.  If these conditions are independent (i.e. `f` is surjective), then the solution
set is the linear subspace `ker f`, whose dimension — the number of degrees of freedom
`F` — satisfies `F + P = C + 2`, that is, `F = C - P + 2`. -/
