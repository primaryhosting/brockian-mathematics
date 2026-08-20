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

def phaseVarCount (C P : ℕ) : ℕ := P * (C - 1) + 2

/-- Number of equilibrium constraints: for each of the `C` components, equality of its
chemical potential across the `P` phases gives `P - 1` independent equations. -/
