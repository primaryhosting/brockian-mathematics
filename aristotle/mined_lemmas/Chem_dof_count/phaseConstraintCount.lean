/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- Number of intensive state variables of a `P`-phase, `C`-component system:
temperature and pressure, together with `C - 1` independent mole fractions in each
of the `P` phases. -/

def phaseConstraintCount (C P : ℕ) : ℕ := C * (P - 1)

/-- Arithmetic core of the phase rule: if the `C * (P - 1)` constraints are independent,
the solution dimension `k` satisfies `k = C - P + 2` (over `ℤ`, so that no truncation of
natural subtraction occurs). -/
