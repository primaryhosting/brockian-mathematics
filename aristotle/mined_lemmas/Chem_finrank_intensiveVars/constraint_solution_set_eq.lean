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


theorem constraint_solution_set_eq {C P : ℕ}
    (A : IntensiveVars C P →ₗ[ℝ] ConstraintValues C P) (hA : Function.Surjective A)
    (bb : ConstraintValues C P) :
    ∃ v₀ : IntensiveVars C P,
      {v : IntensiveVars C P | A v = bb} = (fun w => v₀ + w) '' (LinearMap.ker A : Set _) := by
  obtain ⟨v₀, hv₀⟩ := hA bb
  refine ⟨v₀, ?_⟩
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe, LinearMap.mem_ker]
  constructor
  · intro h
    exact ⟨v - v₀, by simp [map_sub, h, hv₀], by abel⟩
  · rintro ⟨w, hw, rfl⟩
    simp [map_add, hw, hv₀]

/-- The concrete linearised thermodynamic constraint map.  For coefficients `a i j`, `b i j`,
`g i j` describing the (linearised) chemical potential
`μ i j = a i j * T + b i j * p + g i j * x j i`
of component `i` in phase `j`, the constraints are the total mole fraction `∑ i, x j i` of each
phase `j` together with the differences `μ i j - μ i (j+1)` of chemical potentials between
consecutive phases. -/
