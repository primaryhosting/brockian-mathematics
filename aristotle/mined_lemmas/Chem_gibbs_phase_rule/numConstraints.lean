import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Module

/-- Number of intensive state variables used to describe a system of `C` chemical
components distributed over `P` phases: temperature, pressure, and the `C` mole
fractions of each of the `P` phases. -/

def numConstraints (C P : ℕ) : ℕ := P + C * (P - 1)

/-- The counting identity behind the phase rule:
`(2 + P·C) - (P + C·(P-1)) = C - P + 2`. -/
