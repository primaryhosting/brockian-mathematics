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

def numVariables (C P : ℕ) : ℕ := 2 + P * C

/-- Number of equilibrium constraints on the intensive variables: one normalisation
condition `∑ᵢ xᵢⱼ = 1` per phase (`P` of them), together with the equalities of the
chemical potential of each component across the phases (`C * (P - 1)` of them). -/
