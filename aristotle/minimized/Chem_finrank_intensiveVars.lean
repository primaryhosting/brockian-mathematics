/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is repeated
-- as a module docstring immediately after the import.)

import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

The Gibbs phase rule states that a system with `C` chemical components distributed over
`P` coexisting phases has

  `F = C - P + 2`

thermodynamic degrees of freedom.  The classical derivation is a dimension count:

* the intensive state of the system is described by the temperature `T`, the pressure `p`
  and the mole fractions `x j i` of component `i` in phase `j`, i.e. by a point of the
  `2 + P * C`-dimensional real vector space `Chem.IntensiveVars C P`;
* the state is subject to `P` normalisation constraints (one per phase, `∑ i, x j i = 1`)
  and to `C * (P - 1)` phase-equilibrium constraints (equality of the chemical potential of
  each component in consecutive phases), i.e. the constraints are the fibre of a linear map
  into the `P + (P - 1) * C`-dimensional space `Chem.ConstraintValues C P`;
* if the constraints are independent (the constraint map is surjective), the set of admissible
  states is an affine subspace whose direction is the kernel of the constraint map, and
  rank–nullity gives
  `dim = (2 + P * C) - (P + (P - 1) * C) = C - P + 2`.

`Chem.gibbs_phase_rule` is exactly this statement.  `Chem.constraintMap` provides the
concrete (linearised) thermodynamic constraint map, and
`Chem.gibbs_phase_rule_one_component_two_phases` instantiates everything in the
one-component/two-phase case (a coexistence curve, `F = 1`), showing that the independence
hypothesis is not vacuous.
-/

open Module

namespace Chem

/-- Intensive state variables of a `C`-component, `P`-phase system: the temperature, the
pressure, and the mole fraction `x j i` of component `i` in phase `j`. -/
abbrev IntensiveVars (C P : ℕ) : Type := ℝ × ℝ × (Fin P → Fin C → ℝ)

/-- Values of the constraints imposed on a `C`-component, `P`-phase system: one normalisation
constraint per phase, and, for each of the `P - 1` consecutive pairs of phases, one
phase-equilibrium constraint per component. -/
abbrev ConstraintValues (C P : ℕ) : Type := (Fin P → ℝ) × (Fin (P - 1) → Fin C → ℝ)

theorem finrank_intensiveVars (C P : ℕ) :
    finrank ℝ (IntensiveVars C P) = 2 + P * C := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_pi_fintype]
  simp
  ring
